(* ::Package:: *)

(* ::Title:: *)
(*Amplitude calculator from a given Lagrangian*)


(* ::Text:: *)
(* by Feng-Kun Guo (HISKP, Uni. Bonn)*)
(* fkguo@hiskp.uni-bonn.de*)
(* April - May, Sept. 2011*)
(* Fermions included in March - April 2012*)


(* ::Section::Closed:: *)
(*Output setting*)


(* The codes FCTBox and FCtotr are copied from FeynCalc.m by Rolf Mertig. The functions are called TBox and totr there. *)
(*---------Beginning of FeynCalc codes---------*)
FCTBox[]="\[Null]";
FCTBox[a_]:=FCtotr[a];
FCTBox[a_,b__] := RowBox @ Map[(ToBoxes @@ {#, TraditionalForm})&, {a, b}];
FCtotr[Subscript[y_,in__Integer]]:=SubscriptBox[FCtotr[y],RowBox[{in}]];
FCtotr[y_Symbol]:=If[FormatValues[Evaluate[y]]==={},ToString[y],ToBoxes[y,TraditionalForm],y];
FCtotr[y_String]:=y;
FCtotr[y_]:=ToBoxes[y,TraditionalForm]/;Head[y]=!=Symbol;

(* From FeynCalc *)
Unprotect[SuperscriptBox];
SuperscriptBox[FormBox[SubscriptBox[x_,y_],f_],z_] :=
SubsuperscriptBox[x, y, z]
Protect[SuperscriptBox]

(*---------End of FeynCalc codes---------*)

Unprotect[SubscriptBox];
SubscriptBox[FormBox[SuperscriptBox[x_,y_],f_],z_] :=
SubsuperscriptBox[x, z, y]
Protect[SubscriptBox]

pi/:MakeBoxes[pi,TraditionalForm]:="\[Pi]"
pi0/:MakeBoxes[pi0,TraditionalForm]:=SuperscriptBox["\[Pi]","0"]
pip/:MakeBoxes[pip,TraditionalForm]:=SuperscriptBox["\[Pi]","+"]
pim/:MakeBoxes[pim,TraditionalForm]:=SuperscriptBox["\[Pi]","-"]
K0/:MakeBoxes[K0,TraditionalForm]:=SuperscriptBox["K","0"]
K0bar/:MakeBoxes[K0bar,TraditionalForm]:=SuperscriptBox[OverscriptBox["K","_"],"0"]
Kp/:MakeBoxes[Kp,TraditionalForm]:=SuperscriptBox["K","+"]
Km/:MakeBoxes[Km,TraditionalForm]:=SuperscriptBox["K","-"]
eta/:MakeBoxes[eta,TraditionalForm]:="\[Eta]"
etap/:MakeBoxes[etap,TraditionalForm]:=SuperscriptBox["\[Eta]"," \[Prime]"]
eta0/:MakeBoxes[eta0,TraditionalForm]:=SubscriptBox["\[Eta]","0"]
eta8/:MakeBoxes[eta8,TraditionalForm]:=SubscriptBox["\[Eta]","8"]

Fpi/:MakeBoxes[Fpi,TraditionalForm]:=SubscriptBox["F","\[Pi]"]
F0/:MakeBoxes[F0,TraditionalForm]:=SubscriptBox["F","0"]
B0/:MakeBoxes[B0,TraditionalForm]:=SubscriptBox["B","0"]
mhat/:MakeBoxes[mhat,TraditionalForm]:=OverscriptBox["m","^"]
mq/:MakeBoxes[mq[q_],TraditionalForm]:=SubscriptBox["m",FCTBox[q]]

Nc/:MakeBoxes[Nc,TraditionalForm]:=SubscriptBox["N","c"]
Nf/:MakeBoxes[Nf,TraditionalForm]:=SubscriptBox["N","f"]

L/:MakeBoxes[L[i_],TraditionalForm]:=SubscriptBox["L",FCTBox[i]]
m/:MakeBoxes[m[i_],TraditionalForm]:=SubscriptBox["m",FCTBox[i]]
M/:MakeBoxes[M[f_],TraditionalForm]:=SubscriptBox["M",FCTBox[f]]
p/:MakeBoxes[p[i_],TraditionalForm]:=SubscriptBox["p",FCTBox[i]]
s/:MakeBoxes[s[i_],TraditionalForm]:=SubscriptBox["s",FCTBox[i]]
Lr/:MakeBoxes[Lr[i_],TraditionalForm]:=SubsuperscriptBox["L",FCTBox[i],"r"]

rho/:MakeBoxes[rho,TraditionalForm]:="\[Rho]"
rho0/:MakeBoxes[rho0,TraditionalForm]:=SuperscriptBox["\[Rho]","0"]
rhop/:MakeBoxes[rhop,TraditionalForm]:=SuperscriptBox["\[Rho]","+"]
rhom/:MakeBoxes[rhom,TraditionalForm]:=SuperscriptBox["\[Rho]","-"]
omega/:MakeBoxes[omega,TraditionalForm]:="\[Omega]"
phi/:MakeBoxes[phi,TraditionalForm]:="\[Phi]"
Kstar0/:MakeBoxes[Kstar0,TraditionalForm]:=SuperscriptBox["K","*0"]
Kstar0bar/:MakeBoxes[Kstar0bar,TraditionalForm]:=SuperscriptBox[OverscriptBox["K","_"],"*0"]
Kstarp/:MakeBoxes[Kstarp,TraditionalForm]:=SuperscriptBox["K","*+"]
Kstarm/:MakeBoxes[Kstarm,TraditionalForm]:=SuperscriptBox["K","*-"]

f2/:MakeBoxes[f2,TraditionalForm]:=SubscriptBox["f","2"]
a20/:MakeBoxes[a20,TraditionalForm]:=SubsuperscriptBox["a","2","0"]
a2p/:MakeBoxes[a2p,TraditionalForm]:=SubsuperscriptBox["a","2","+"]
a2m/:MakeBoxes[a2m,TraditionalForm]:=SubsuperscriptBox["a","2","-"]
K20/:MakeBoxes[K20,TraditionalForm]:=SubsuperscriptBox["K","2","0"]
K20bar/:MakeBoxes[K20bar,TraditionalForm]:=SubsuperscriptBox[OverscriptBox["K","_"],"2","0"]
K2p/:MakeBoxes[K2p,TraditionalForm]:=SubsuperscriptBox["K","2","+"]
K2m/:MakeBoxes[K2m,TraditionalForm]:=SubsuperscriptBox["K","2","-"]
f2p/:MakeBoxes[f2p,TraditionalForm]:=SubsuperscriptBox["f","2"," \[Prime]"]

rho0/:MakeBoxes[rho0[\[Mu]__],TraditionalForm]:=SubsuperscriptBox["\[Rho]",FCTBox[\[Mu]],"0"]
rhop/:MakeBoxes[rhop[\[Mu]__],TraditionalForm]:=SubsuperscriptBox["\[Rho]",FCTBox[\[Mu]],"+"]
rhom/:MakeBoxes[rhom[\[Mu]__],TraditionalForm]:=SubsuperscriptBox["\[Rho]",FCTBox[\[Mu]],"-"]
omega/:MakeBoxes[omega[\[Mu]__],TraditionalForm]:=SubscriptBox["\[Omega]",FCTBox[\[Mu]]]
phi/:MakeBoxes[phi[\[Mu]__],TraditionalForm]:=SubscriptBox["\[Phi]",FCTBox[\[Mu]]]
Kstar0/:MakeBoxes[Kstar0[\[Mu]__],TraditionalForm]:=SubsuperscriptBox["K",FCTBox[\[Mu]],"*0"]
Kstar0bar/:MakeBoxes[Kstar0bar[\[Mu]__],TraditionalForm]:=SubsuperscriptBox[OverscriptBox["K","_"],FCTBox[\[Mu]],"*0"]
Kstarp/:MakeBoxes[Kstarp[\[Mu]__],TraditionalForm]:=SubsuperscriptBox["K",FCTBox[\[Mu]],"*+"]
Kstarm/:MakeBoxes[Kstarm[\[Mu]__],TraditionalForm]:=SubsuperscriptBox["K",FCTBox[\[Mu]],"*-"]

f2/:MakeBoxes[f2[\[Mu]__],TraditionalForm]:=SubscriptBox["f",RowBox[{"2",FCTBox[\[Mu]]}]]
a20/:MakeBoxes[a20[\[Mu]__],TraditionalForm]:=SubsuperscriptBox["a",RowBox[{"2",FCTBox[\[Mu]]}],"0"]
a2p/:MakeBoxes[a2p[\[Mu]__],TraditionalForm]:=SubsuperscriptBox["a",RowBox[{"2",FCTBox[\[Mu]]}],"+"]
a2m/:MakeBoxes[a2m[\[Mu]__],TraditionalForm]:=SubsuperscriptBox["a",RowBox[{"2",FCTBox[\[Mu]]}],"-"]
K20/:MakeBoxes[K20[\[Mu]__],TraditionalForm]:=SubsuperscriptBox["K",RowBox[{"2",FCTBox[\[Mu]]}],"0"]
K20bar/:MakeBoxes[K20bar[\[Mu]__],TraditionalForm]:=SubsuperscriptBox[OverscriptBox["K","_"],RowBox[{"2",FCTBox[\[Mu]]}],"0"]
K2p/:MakeBoxes[K2p[\[Mu]__],TraditionalForm]:=SubsuperscriptBox["K",RowBox[{"2",FCTBox[\[Mu]]}],"+"]
K2m/:MakeBoxes[K2m[\[Mu]__],TraditionalForm]:=SubsuperscriptBox["K",RowBox[{"2",FCTBox[\[Mu]]}],"-"]
f2p/:MakeBoxes[f2p[\[Mu]__],TraditionalForm]:=SubsuperscriptBox["f",RowBox[{"2",FCTBox[\[Mu]]}]," \[Prime]"]

photon/:MakeBoxes[photon[\[Mu]_],TraditionalForm]:=SubscriptBox["A",FCTBox[\[Mu]]]
photon/:MakeBoxes[photon,TraditionalForm]:="\[Gamma]"


Metric/:MakeBoxes[Metric[\[Mu]_,\[Nu]_] ,TraditionalForm] :=SuperscriptBox["g",FCTBox[\[Mu],\[Nu]]]
Levicivita\[Epsilon]/:MakeBoxes[Levicivita\[Epsilon][x__] ,TraditionalForm] := SubscriptBox["\[Epsilon]", FCTBox[x]]
(* Express the partial derivative on fields in term of \[PartialD]^\[Mu] *)
pd/: MakeBoxes[pd[x_,\[Mu]_] ,TraditionalForm] := RowBox[{SuperscriptBox["\[PartialD]", FCTBox[\[Mu]]],FCTBox[x]}];
pd/: MakeBoxes[pd[x_,\[Mu]_,\[Nu]_] ,TraditionalForm] := RowBox[{SuperscriptBox["\[PartialD]", FCTBox[\[Mu]]],SuperscriptBox["\[PartialD]", FCTBox[\[Nu]]],FCTBox[x]}];

(*
(* Using \[RightVector] for nonrelativistic notation *)
momentum/: MakeBoxes[momentum[p_,\[Mu]___] ,TraditionalForm] := If[$NonRelativistic==False,
SuperscriptBox[FCTBox[p], FCTBox[\[Mu]]],
SuperscriptBox[OverscriptBox[FCTBox[p],"\[RightVector]"], FCTBox[\[Mu]]]]
polarization/:MakeBoxes[polarization[p_,x___] ,TraditionalForm] :=If[$NonRelativistic==False,
RowBox[{ SubscriptBox["\[CurlyEpsilon]", FCTBox[x]],"(",FCTBox[p],")"}],
RowBox[{ SuperscriptBox["\[CurlyEpsilon]", FCTBox[x]],"(",FCTBox[p],")"}]];
*)

(* Using bold face for nonrelativistic notation *)
momentum/: MakeBoxes[momentum[p_,\[Mu]___] ,TraditionalForm] :=Module[{str,stri,strf},
str=ToString[p];If[StringMatchQ[str,__~~(c_?DigitQ)],stri=StringDrop[str,-1];strf=StringTake[str,-1];
 If[$NonRelativistic==False,
SubsuperscriptBox[FCTBox[stri],FCTBox[strf], FCTBox[\[Mu]]],
SubsuperscriptBox[StyleBox[FCTBox[stri],FontWeight->Bold],FCTBox[strf], FCTBox[\[Mu]]]],
If[$NonRelativistic==False,
SuperscriptBox[FCTBox[p], FCTBox[\[Mu]]],
SuperscriptBox[StyleBox[FCTBox[p],FontWeight->Bold], FCTBox[\[Mu]]]]
]]
polarization/:MakeBoxes[polarization[p_,x___] ,TraditionalForm] :=If[$NonRelativistic==False,
RowBox[{ SubscriptBox["\[CurlyEpsilon]", FCTBox[x]],"(",FCTBox[p],")"}],
RowBox[{ SuperscriptBox[StyleBox["\[CurlyEpsilon]",FontWeight->Bold], FCTBox[x]],"(",FCTBox[p],")"}]];

sp/:MakeBoxes[sp[x_,y_],TraditionalForm] := If[$NonRelativistic==False,
 RowBox[{FCTBox[x],"\[CenterDot]", FCTBox[y]}],
RowBox[{StyleBox[FCTBox[x],FontWeight->Bold],"\[CenterDot]", StyleBox[FCTBox[y],FontWeight->Bold]}]];
sp/:MakeBoxes[sp[x_,x_],TraditionalForm] :=If[$NonRelativistic==False,
 SuperscriptBox[FCTBox[x],"2"],
SuperscriptBox[StyleBox[FCTBox[x],FontWeight->Bold], "2"]];

sp/:MakeBoxes[sp[x_Plus,y_],TraditionalForm] := RowBox[{"(",FCTBox[x],")","\[CenterDot]", FCTBox[y]}];
sp/:MakeBoxes[sp[x_,y_Plus],TraditionalForm] := RowBox[{FCTBox[x],"\[CenterDot]", "(",FCTBox[y],")"}]
sp/:MakeBoxes[sp[x_Plus,y_Plus],TraditionalForm] := RowBox[{"(",FCTBox[x],")","\[CenterDot]", "(",FCTBox[y],")"}]
sp/:MakeBoxes[sp[x_Plus,x_Plus],TraditionalForm] := SuperscriptBox[RowBox[{"(",FCTBox[x],")"}],"2"]

p1/:MakeBoxes[p1,TraditionalForm]:=SubscriptBox["p","1"]
p2/:MakeBoxes[p2,TraditionalForm]:=SubscriptBox["p","2"]
p3/:MakeBoxes[p3,TraditionalForm]:=SubscriptBox["p","3"]
p4/:MakeBoxes[p4,TraditionalForm]:=SubscriptBox["p","4"]
p5/:MakeBoxes[p5,TraditionalForm]:=SubscriptBox["p","5"]
p6/:MakeBoxes[p6,TraditionalForm]:=SubscriptBox["p","6"]
s12/:MakeBoxes[s12,TraditionalForm]:=SubscriptBox["s","12"]
s34/:MakeBoxes[s34,TraditionalForm]:=SubscriptBox["s","34"]
s14/:MakeBoxes[s14,TraditionalForm]:=SubscriptBox["s","14"]
s23/:MakeBoxes[s23,TraditionalForm]:=SubscriptBox["s","23"]
s13/:MakeBoxes[s13,TraditionalForm]:=SubscriptBox["s","13"]
s24/:MakeBoxes[s24,TraditionalForm]:=SubscriptBox["s","24"]
s124/:MakeBoxes[s124,TraditionalForm]:=SubscriptBox["s","124"]
s234/:MakeBoxes[s234,TraditionalForm]:=SubscriptBox["s","234"]

LFA0/:MakeBoxes[LFA0,TraditionalForm]:=SubscriptBox["A","0"]
LFA00/:MakeBoxes[LFA00,TraditionalForm]:=SubscriptBox["A","00"]
LFB0/:MakeBoxes[LFB0,TraditionalForm]:=SubscriptBox["B","0"]
LFB1/:MakeBoxes[LFB1,TraditionalForm]:=SubscriptBox["B","1"]
LFB00/:MakeBoxes[LFB00,TraditionalForm]:=SubscriptBox["B","00"]
LFB11/:MakeBoxes[LFB11,TraditionalForm]:=SubscriptBox["B","11"]
LFB001/:MakeBoxes[LFB001,TraditionalForm]:=SubscriptBox["B","001"]
LFB111/:MakeBoxes[LFB111,TraditionalForm]:=SubscriptBox["B","111"]
LFB0000/:MakeBoxes[LFB0000,TraditionalForm]:=SubscriptBox["B","0000"]
LFB0011/:MakeBoxes[LFB0011,TraditionalForm]:=SubscriptBox["B","0011"]
LFB1111/:MakeBoxes[LFB1111,TraditionalForm]:=SubscriptBox["B","1111"]

Jbar/:MakeBoxes[Jbar,TraditionalForm]:=OverscriptBox["J","_"]


Proton/:MakeBoxes[Proton,TraditionalForm]:="p"
Neutron/:MakeBoxes[Neutron,TraditionalForm]:="n"
Format[Sigmap]="\!\(\*SuperscriptBox[\(\[CapitalSigma]\), \(+\)]\)";
Format[Sigma0]="\!\(\*SuperscriptBox[\(\[CapitalSigma]\), \(0\)]\)";
Format[Sigmam]="\!\(\*SuperscriptBox[\(\[CapitalSigma]\), \(-\)]\)";
Format[Xi0]="\!\(\*SuperscriptBox[\(\[CapitalXi]\), \(0\)]\)";
Format[Xim]="\!\(\*SuperscriptBox[\(\[CapitalXi]\), \(-\)]\)";
Lambda/:MakeBoxes[Lambda,TraditionalForm]:="\[CapitalLambda]"
Format[Sigma,TraditionalForm]="\[CapitalSigma]";
Format[Xi,TraditionalForm]="\[CapitalXi]";
BOctet/:MakeBoxes[BOctet,TraditionalForm]:="B"

Bar/:MakeBoxes[Bar[x_],TraditionalForm]:=OverscriptBox[FCTBox[x],"_"]
IMatrix/:MakeBoxes[IMatrix[i_],TraditionalForm]:=SubscriptBox["\[DoubleStruckOne]",FCTBox[i]]
Paulisigma/:MakeBoxes[Paulisigma[i_],TraditionalForm]:=SuperscriptBox["\[Sigma]",FCTBox[i]]
GammaMatrix/: MakeBoxes[GammaMatrix[\[Mu]_] ,TraditionalForm] := SuperscriptBox["\[Gamma]",FCTBox[\[Mu]]];
Diracsigma/: MakeBoxes[Diracsigma[i__],TraditionalForm]:=SuperscriptBox["\[Sigma]",FCTBox[i]]

(* Indices[m,{i,j}] *)
Indices/:MakeBoxes[Indices[m_,i_List],TraditionalForm]:=SubscriptBox[RowBox[{"(",FCTBox[m],")"}],FCTBox[Sequence@@i]]

SpinorU/: MakeBoxes[SpinorU,TraditionalForm] := "u"
SpinorV/: MakeBoxes[SpinorV,TraditionalForm] := "v"

(* Format[IMatrix]:="\[ScriptCapitalI]" *)
SpinorDot/:Format[Unevaluated[SpinorDot[a__]]]:=HoldForm[CenterDot[a]]



(* ::Section::Closed:: *)
(*General purpose functions*)
(* ----------Codes of PrintTime from Maeder's book---------- *)


SetAttributes[PrintTime,HoldAll]
PrintTime[exp_]:=With[{timing=Timing[exp]},Print["Time used: ", timing[[1]], " seconds" ];timing[[2]] ]


SetAttributes[PrintAbsoluteTime,HoldAll];
PrintAbsoluteTime[exp_]:=With[{timing=AbsoluteTiming[exp]},Print["Absolute time used: ", SetPrecision[timing[[1]],4], " seconds" ];timing[[2]] ]

(* simplify a summation term by term *)
simplify[exp_Plus] := Simplify[#] & /@ exp
simplify[exp_] := Simplify[exp]

fullSimplify[exp_Plus] := FullSimplify[#] & /@ exp
fullSimplify[exp_] := FullSimplify[exp]



(* ::Section:: *)
(*Deriving amplitudes from a given \[ScriptCapitalL]*)


(* charge *)
Charge[pi0]=0;
Charge[pip]=1;
Charge[pim]=-1;
Charge[eta0]=0;
Charge[eta8]=0;
Charge[K0]=0;
Charge[K0bar]=0;
Charge[Kp]=1;
Charge[Km]=-1;
Charge[eta]=0;
Charge[etap]=0;

(* strangeness *)
Strangeness[pi0]=0;
Strangeness[pip]=0;
Strangeness[pim]=0;
Strangeness[eta0]=0;
Strangeness[eta8]=0;
Strangeness[K0]=1;
Strangeness[K0bar]=-1;
Strangeness[Kp]=1;
Strangeness[Km]=-1;
Strangeness[eta]=0;
Strangeness[etap]=0;

(* for baryons *)
Charge[Proton]=1;
Charge[Neutron]=0;
Charge[Lambda]=0;
Charge[Sigmap]=1;
Charge[Sigmam]=-1;
Charge[Sigma0]=0;
Charge[Xi0]=0;
Charge[Xim]=-1;

Strangeness[Proton]=0;
Strangeness[Neutron]=0;
Strangeness[Lambda]=-1;
Strangeness[Sigmap]=-1;
Strangeness[Sigmam]=-1;
Strangeness[Sigma0]=-1;
Strangeness[Xi0]=-2;
Strangeness[Xim]=-2;


(* Set NonRelativistic option for MomentumProduct. *)
(* If $NonRelativistic=False, \[PartialD] is replaced by -Ip with p being the incoming momentum of the particle.
If $NonRelativistic=True, \[PartialD] will be replaced by Ip. *)
NROption=NonRelativistic:>$NonRelativistic;
Options[MomentumProduct]={NROption};

(* $NonRelativistic also determines the overall sign of the product of two Levi-Civita tensors. *)
(* If $NonRelativistic=False, then it assumes Minkowski space, and the product of two LC tensors bears a minus sign.
If $NonRelativistic=True, then it assumes Euclidean space, no overall sign in the LC product. *)
LCsign=If[$NonRelativistic==False,-1,1];
(* By default, $NonRelativistic=False *)
$NonRelativistic=False;

M[pim]:=M[pip];
M[Km]:=M[Kp];
M[K0bar]:=M[K0];

(* leading order masses of the mesons *)
(MLO[#] := Sqrt[B0 (mq@u + mq@d)]) & /@ {pip, pim, pi0}
(MLO[#] := Sqrt[B0 (mq@u + mq@s)]) & /@ {Kp, Km}
(MLO[#] := Sqrt[B0 (mq@d + mq@s)]) & /@ {K0, K0bar}
MLO[K] := Sqrt[B0 (mhat + mq@s)]
(MLO[#] := Sqrt[B0 (mq@u + mq@d + 4 mq@s)/3]) & /@ {eta, eta8}

(* Options for isospin symmetry *)
M[a_?(MemberQ[{pip,pim,pi0},#]&)]:=M[pi]/;$IsospinSymmetry==True;
M[a_?(MemberQ[{K0,K0bar,Kp,Km},#]&)]:=M[K]/;$IsospinSymmetry==True;
mq[a_?(MemberQ[{u,d},#]&)]:=mhat/;$IsospinSymmetry==True;

(* isospin symmetric case *)
M[a_?(MemberQ[{Proton,Neutron},#]&)]:=M[N]/;$IsospinSymmetry==True;
m[a_?(MemberQ[{Proton,Neutron},#]&)]:=m[N]/;$IsospinSymmetry==True;
M[a_?(MemberQ[{Sigmap,Sigma0,Sigmam},#]&)]:=M[Sigma]/;$IsospinSymmetry==True;
m[a_?(MemberQ[{Sigmap,Sigma0,Sigmam},#]&)]:=m[Sigma]/;$IsospinSymmetry==True;
M[a_?(MemberQ[{Xim,Xi0},#]&)]:=M[Xi]/;$IsospinSymmetry==True;
m[a_?(MemberQ[{Xim,Xi0},#]&)]:=m[Xi]/;$IsospinSymmetry==True;

$IsospinSymmetry=True;



(* ::Subsection:: *)
(*Definitions of fields, momentum, polarization, metric and Levi-Civita tensor etc.*)


(* Declare physical quantities to be constant whose pd[] is 0. *)
PhysicalQuantities={e,F0,Fpi,B0,Nc,Nf};
SetAttributes[#,Constant]&/@PhysicalQuantities;
(* codes from R.Maeder's book, p .183 *)
constantQ[c_Symbol]:=MemberQ[Attributes[c],Constant]
constantQ[c_?NumericQ]:=True
(* Let L[i],M[i],m[i] be constants. *)
constantQ[L[i_]]:=True
constantQ[M[i_]]:=True
constantQ[m[i_]]:=True
constantQ[mq[i_]]:=True
constantQ[F0^_]=True;
constantQ[B0^_]=True;

constantQ[f_?FieldQ[i__]]:=False;

(* List of Goldstone bosons *)

Module[{octet},
	octet={pi0,pip,pim,K0,K0bar,Kp,Km,eta,etap,eta0,eta8};
	Which[
		Head[GBList]===Symbol, GBList = octet,
		Head[GBList]===List, GBList = UnsortedUnion@Join[octet,GBList]]
	];
(* GBQ[c_]:=MemberQ[GBList,c] *)
(* Clear[GBQ]
Evaluate[GBQ[#]&/@GBList] = Table[True, {Length[GBList]}];
GBQ[a_]:=False; *)
GBQ[a_]:=False
(GBQ[#]:=True)&/@GBList;

(* List of pseudosclar mesons *)
Module[{octet},
	octet={pi0,pip,pim,K0,K0bar,Kp,Km,eta,etap,eta0,eta8};
	Which[
		Head[PseudoscalarList]===Symbol, PseudoscalarList = octet,
		Head[PseudoscalarList]===List, PseudoscalarList = UnsortedUnion@Join[octet,PseudoscalarList]]
	];

(* List of scalar fields *)
If[	Head[ScalarList]===Symbol, ScalarList = {} ] ;

(* List 0f spin-0 fields *)
Spin0List:=Flatten@Join[PseudoscalarList,ScalarList]
(* List of Vector mesons *)
VectorList={rho0,rhop,rhom,Kstar0,Kstar0bar,Kstarp,Kstarm,omega,phi,photon};
(* List of tensor mesons *)
TensorList={a20,a2p,a2m,K20,K20bar,K2p,K2m,f2,f2p};

Module[{octet},
	octet={Proton,Neutron,Sigmap,Sigma0,Sigmam,Xi0,Xim,Lambda};
	Which[
		Head[Fermionlist]===Symbol, Fermionlist = octet,
		Head[Fermionlist]===List, Fermionlist = UnsortedUnion@Join[octet,Fermionlist]]
	];

(* set Listable attribute for Bar before FieldList *)
SetAttributes[Bar,{Listable}];

FieldList:=Flatten@Join[PseudoscalarList,VectorList,TensorList,ScalarList, Fermionlist, Bar[Fermionlist]];

(* The function returns True if c is a field which belongs to the given list, otherwise False *)
(* FieldQ[c_]:=MemberQ[FieldList,c] *)
FieldQ[_] := False
(FieldQ[#] := True) &/@Evaluate[FieldList];
(* This function returns True if the field belongs to PseudoscalarList with spin 0 *)
(* scalarQ[c_]:=MemberQ[Spin0List,c] *)
scalarQ[_] := False
(scalarQ[#] := True) &/@Evaluate[Spin0List];
(* This function returns True if the field belongs to VectorList with spin 1 *)
(* vectorQ[c_]:=MemberQ[VectorList,c] *)
vectorQ[_] := False
(vectorQ[#] := True) &/@Evaluate[VectorList];
(* This function returns True if the field belongs to TensorList with spin 2 *)
(* tensorQ[c_]:=MemberQ[TensorList,c] *)
tensorQ[_] := False
(tensorQ[#] := True) &/@Evaluate[TensorList];

BosonQ[c_]:= Or[scalarQ[c],vectorQ[c],tensorQ[c]];

(* Attach Lorentz indices to field *)
LorentzIndexed[field_,indices_]:=field/.a_?FieldQ:>a[Sequence@@indices];
(* Set the tensor meson fields to be symmetric *)
SetAttributes[{a20,a2p,a2m,K20,K20bar,K2p,K2m,f2,f2p},Orderless];


SetAttributes[AntiParticle,Listable]
(* AntiParticle[f_]:=Module[{antigb},antigb={pi0,pim,pip,K0bar,K0,Km,Kp,eta,etap,eta0,eta8};Extract[antigb,Position[GBList,f][[1]]]] *)
AntiParticle[pip]=pim; AntiParticle[pim]=pip;
AntiParticle[K0bar]=K0; AntiParticle[K0]=K0bar;
AntiParticle[Kp]=Km; AntiParticle[Km]=Kp;
(AntiParticle[#]=#)&/@{pi0, eta, etap, eta0, eta8};


UnsortedUnion[x__]:=Tally[Flatten[{x}]][[All,1]]
MoreGB[a__]:=Module[{app,lis},
	lis = Flatten[{a}];
	app=AppendTo[GBList,#]&/@lis;
	(*Print["Goldstone bosons include:"];*)
	(GBQ[#]=True)&/@lis;
	(FieldQ[#]=True)&/@lis;
	GBList=UnsortedUnion@app[[-1]]]
MorePseudoscalar[a__]:=Module[{app,lis=Flatten[{a}]},
	app=AppendTo[PseudoscalarList,#]&/@lis;
	(scalarQ[#]=True)&/@lis;
	(FieldQ[#]=True)&/@lis;
	(* Refresh FieldList
	FieldList=Join[UnsortedUnion@PseudoscalarList,VectorList,TensorList,ScalarList];
	Print["Pseudoscalar fields include:"];*)
	PseudoscalarList=UnsortedUnion@app[[-1]]]
MoreScalar[a__]:=Module[{app,lis=Flatten[{a}]},
	app=AppendTo[ScalarList,#]&/@lis;
	(scalarQ[#]=True)&/@lis;
	(FieldQ[#]=True)&/@lis;
	(* Refresh FieldList
	FieldList=Join[PseudoscalarList,VectorList,TensorList,UnsortedUnion@ScalarList];
	Print["Scalar fields include:"];*)
	ScalarList=UnsortedUnion@app[[-1]]]
MoreVector[a__]:=Module[{app,lis=Flatten[{a}]},
	app=AppendTo[VectorList,#]&/@lis;
	(vectorQ[#]=True)&/@lis;
	(FieldQ[#]=True)&/@lis;
	(* Refresh FieldList
	FieldList=Join[PseudoscalarList,UnsortedUnion@VectorList,TensorList,ScalarList];
	Print["Vector fields include:"];*)
	VectorList=UnsortedUnion@app[[-1]]]
MoreTensor[a__]:=Module[{app,lis=Flatten[{a}]},
	app=AppendTo[TensorList,#]&/@lis;
	(tensorQ[#]=True)&/@lis;
	(FieldQ[#]=True)&/@lis;
	(* Refresh FieldList
	FieldList=Join[PseudoscalarList,VectorList,UnsortedUnion@TensorList,ScalarList];
	Print["Tensor fields include:"];*)
	TensorList=UnsortedUnion@app[[-1]]]



(* Define derivative over fields *)
(* SetAttributes[pd,Listable] *)

pd[a_List, args___]:= pd[#,args]&/@a

(* pd[constant]=0 *)
pd[a_?constantQ,\[Mu]___]:=0

(*  taken from R.Maeder's book. It has a better performance than pd[a_+b_,\[Mu]___]:=pd[a,\[Mu]]+pd[b,\[Mu]]. *)
(* Only thread the first argument, so the problem of pd[a,\[Mu]]+pd[b,\[Nu]] giving pd[a+b,\[Mu]+\[Nu]] is removed *)
a:pd[_Plus,___]:=Thread[Unevaluated[a],Plus,1]

pd[a_/;MemberQ[{Times,Dot,NonCommutativeMultiply},Head[a]],x___]:= Plus@@(MapAt[pd[#,x]&, a, #]&/@Range[Length[a]])
pd[a_ ^b_,\[Mu]___]:=b a^(b-1) pd[a,\[Mu]]

(* For Levi-Civita tensor. Antisymmetric. *)
pd/:Levicivita\[Epsilon][\[Alpha]___,\[Mu]_,\[Mu]1___,\[Nu]_,\[Nu]1___] pd[a_,\[Mu]_] pd[a_,\[Nu]_]:=0
(* In canonical order *)
pd/:Levicivita\[Epsilon][i1___,j_,j2___,k_,k3___] pd[v1_,j_] pd[v2_,k_]/;(OrderedQ[{v2,v1}]):=-Levicivita\[Epsilon][i1,j,j2,k,k3] pd[v2,j] pd[v1,k]

tensorpdQ[\[Mu]_,\[Nu]_,a_,b_]:=(Signature[{a,b}]===1)&&OrderedQ[{\[Mu],\[Nu]}]
f2/:f2[\[Mu]_,\[Nu]_] pd[b_,\[Mu]_] pd[a_,\[Nu]_]/;tensorpdQ[\[Mu],\[Nu],a,b]:=f2[\[Mu],\[Nu]] pd[a,\[Mu]] pd[b,\[Nu]]
f2p/:f2p[\[Mu]_,\[Nu]_] pd[b_,\[Mu]_] pd[a_,\[Nu]_]/;tensorpdQ[\[Mu],\[Nu],a,b]:=f2p[\[Mu],\[Nu]] pd[a,\[Mu]] pd[b,\[Nu]]
a20/:a20[\[Mu]_,\[Nu]_] pd[b_,\[Mu]_] pd[a_,\[Nu]_]/;tensorpdQ[\[Mu],\[Nu],a,b]:=a20[\[Mu],\[Nu]] pd[a,\[Mu]] pd[b,\[Nu]]
a2p/:a2p[\[Mu]_,\[Nu]_] pd[b_,\[Mu]_] pd[a_,\[Nu]_]/;tensorpdQ[\[Mu],\[Nu],a,b]:=a2p[\[Mu],\[Nu]] pd[a,\[Mu]] pd[b,\[Nu]]
a2m/:a2m[\[Mu]_,\[Nu]_] pd[b_,\[Mu]_] pd[a_,\[Nu]_]/;tensorpdQ[\[Mu],\[Nu],a,b]:=a2m[\[Mu],\[Nu]] pd[a,\[Mu]] pd[b,\[Nu]]
K20/:K20[\[Mu]_,\[Nu]_] pd[b_,\[Mu]_] pd[a_,\[Nu]_]/;tensorpdQ[\[Mu],\[Nu],a,b]:=K20[\[Mu],\[Nu]] pd[a,\[Mu]] pd[b,\[Nu]]
K20bar/:K20bar[\[Mu]_,\[Nu]_] pd[b_,\[Mu]_] pd[a_,\[Nu]_]/;tensorpdQ[\[Mu],\[Nu],a,b]:=K20bar[\[Mu],\[Nu]] pd[a,\[Mu]] pd[b,\[Nu]]
K2p/:K2p[\[Mu]_,\[Nu]_] pd[b_,\[Mu]_] pd[a_,\[Nu]_]/;tensorpdQ[\[Mu],\[Nu],a,b]:=K2p[\[Mu],\[Nu]] pd[a,\[Mu]] pd[b,\[Nu]]
K2m/:K2m[\[Mu]_,\[Nu]_] pd[b_,\[Mu]_] pd[a_,\[Nu]_]/;tensorpdQ[\[Mu],\[Nu],a,b]:=K2m[\[Mu],\[Nu]] pd[a,\[Mu]] pd[b,\[Nu]]

(* Let \!\(
\*SubscriptBox[\(\[PartialD]\), \(\[Nu]\)]\(
\*SubscriptBox[\(\[PartialD]\), \(\[Mu]\)]\ \(\(=\)\(\ \)\(
\*SubscriptBox[\(\[PartialD]\), \(\[Mu]\)]
\*SubscriptBox[\(\[PartialD]\), \(\[Nu]\)]\)\)\)\) *)
pd[pd[a_,\[Mu]_],\[Nu]_] /;(OrderedQ[{\[Mu],\[Nu]}]):=pd[pd[a,\[Nu]],\[Mu]]
Levicivita\[Epsilon]/:Levicivita\[Epsilon][\[Alpha]___,\[Mu]_,\[Mu]1___,\[Nu]_,\[Nu]1___] pd[pd[a_,\[Mu]_],\[Nu]_] :=0

SetAttributes[momentum,Listable]
SetAttributes[sp,Orderless]
(*momentum[a_+b_,\[Mu]___]:=momentum[a,\[Mu]]+momentum[b,\[Mu]]*)
a:momentum[_Plus,___]:=Thread[Unevaluated[a],Plus,1]
momentum[a_?constantQ b_,\[Mu]___]:=a momentum[b,\[Mu]]

momentum[0,i___]:=0

momentum/:Levicivita\[Epsilon][\[Alpha]___,\[Mu]_,\[Mu]1___,\[Nu]_,\[Nu]1___] momentum[a__,\[Mu]_] momentum[a__,\[Nu]_]:=0
(* In canonical order *)
momentum/:Levicivita\[Epsilon][i1___,j_,j2___,k_,k3___] momentum[v1__,j_] momentum[v2__,k_]/;(OrderedQ[{v2,v1}]):=
-Levicivita\[Epsilon][i1,j,j2,k,k3] momentum[v2,j] momentum[v1,k]

(* momentum contraction *)
(* use __ instead of _ to allow momentum[p,1,\[Mu]] represent p1... *)
momentum/:momentum[p1_,\[Mu]_Symbol] momentum[p2_,\[Mu]_]:=sp[p1,p2]
momentum/:Power[momentum[p1_,\[Mu]_Symbol],2]:=sp[p1,p1]
momentum/:sp[momentum[p1_],momentum[p2_]]:=sp[p1,p2]
momentum/:sp[momentum[p1_],polarization[p2_]]:=sp[p1,polarization[p2]]
sp[0,x_]:=0

(* Set Expand rules for sp. *)
spExpand[ exp_]:=Expand[ exp//.sp[p1_,pi_]:>Distribute[sp[p1,pi]] ]
sp/:Expand[sp[p1_,pi_]]:=Distribute[sp[p1,pi]]//Expand
sp[a_?constantQ p1_, p2_]:=a sp[p1,p2]

(* In canonical order of momentum *)
polarization/:Levicivita\[Epsilon][i1___,j_,j4___,k_,k3___] polarization[p_,j1___,j_,j2___] polarization[q_,k1___,k_,k2___]/;Signature[{q,p}]===1:=
-Levicivita\[Epsilon][i1,j,j4,k,k3] polarization[q,k1,j,k2] polarization[p,j1,k,j2]
polarization/:Levicivita\[Epsilon][i1___,j_,j4___,k_,k3___] polarization[p_,j_,j2___] polarization[p_,k_,j2___]:=0
polarization/: momentum[p1_,\[Mu]_Symbol] polarization[p2_,\[Mu]_]:=sp[momentum[p1],polarization[p2]]
polarization/: polarization[p1_,\[Mu]_Symbol] polarization[p2_,\[Mu]_]:=sp[polarization[p1],polarization[p2]]


(* added on 27.02.2020; put momentum before polarization when whey are contracted with a Leci-Civita tensor *)
polarization/:Levicivita\[Epsilon][i1___,j_,j4___,k_,k3___] momentum[q__,k_] polarization[p_,j1___,j_,j2___] :=-Levicivita\[Epsilon][i1,j,j4,k,k3] momentum[q,j] polarization[p,j1,k,j2]


(* Remove Head momentum inside polarization *)
polarization[x_,\[Mu]___]/;(!StringFreeQ[ToString[x],"momentum"]):=polarization[x/.momentum[y_]:>y,\[Mu]]

(* Metric tensor *)
SetAttributes[Metric,Orderless]
Metric/:Metric[\[Mu]_,\[Nu]_] polarization[k_,\[Alpha]___,\[Mu]_] polarization[q_,\[Beta]___,\[Nu]_]:=polarization[k,\[Alpha],#] polarization[q,\[Beta],#]&[First[Sort[{\[Mu],\[Nu]}]]]
Metric/:Metric[\[Mu]_,\[Nu]_] polarization[k_,\[Mu]_,\[Alpha]__] polarization[q_,\[Nu]_,\[Beta]__]:=polarization[k,#,\[Alpha]] polarization[q,#,\[Beta]]&[First[Sort[{\[Mu],\[Nu]}]]]
Metric/:Metric[\[Mu]_,\[Nu]_] polarization[k_,\[Mu]_] polarization[q_,\[Nu]_,\[Beta]__]:=polarization[k,#] polarization[q,#,\[Beta]]&[First[Sort[{\[Mu],\[Nu]}]]]
Metric/:Metric[\[Mu]_,\[Nu]_] momentum[p1_,\[Mu]_]:= momentum[p1,\[Nu]]
Metric/:Metric[\[Mu]_,\[Nu]_] polarization[p1_,\[Mu]_]:= polarization[p1,\[Nu]]
Metric/:Metric[\[Mu]_,\[Nu]_] momentum[p1_,\[Mu]_] momentum[p2_,\[Nu]_]:=sp[p1,p2]
Metric/:Metric[\[Mu]_,\[Nu]_] momentum[p1_,\[Mu]_] polarization[p2_,\[Nu]_]:=sp[p1,polarization[p2]]
Metric/:Metric[\[Mu]_,\[Nu]_] momentum[p1_,\[Mu]_] polarization[p2_,\[Rho]_,\[Nu]_]:=momentum[p1,#] polarization[p2,\[Rho],#]&[First[Sort[{\[Mu],\[Nu]}]]]
Metric/:Metric[\[Mu]_,\[Nu]_] momentum[p1_,\[Mu]_] polarization[p2_,\[Nu]_,\[Rho]_]:=momentum[p1,#] polarization[p2,\[Rho],#]&[First[Sort[{\[Mu],\[Nu]}]]]
Metric/:Metric[j_,k_] Levicivita\[Epsilon][i1___,j_,j2___,k_,k3___]:=0
Metric/:Metric[\[Mu]_,\[Nu]_] Metric[\[Mu]_,\[Alpha]_] :=Metric[\[Alpha],\[Nu]]
(* In d dimensions, the default value is d=4. In d dimensions, Metric should be used with 3 arguments. *)
Metric/:Metric[\[Mu]_,\[Nu]_,d_:4] Metric[\[Mu]_,\[Nu]_,d_:4] :=d
Metric/:Metric[\[Mu]_,\[Nu]_,d_:4]^2:=d
Metric/:Metric[\[Mu]_,\[Mu]_,d_:4]:=d

Levicivita\[Epsilon]/:Levicivita\[Epsilon][i___, i1_, j___] Metric[i1_, i2_] := Levicivita\[Epsilon][i, i2, j]


Unprotect[KroneckerDelta];
KroneckerDelta[i_,i_]:=If[$NonRelativistic==True,3,HoldForm@KroneckerDelta[i,i]]
Protect[KroneckerDelta];

(* Product of two Levi-Civita tensors *)
(*--- Ref: The Mathematica Guidebook -- Programming by M. Trott ---*)
(* Now in 3+1 Minkowski space, multiplying -1 for the product. E.g., one should have Subscript[\[Epsilon], \[Mu]\[Nu]\[Alpha]\[Beta]] \[Epsilon]^\[Mu]\[Nu]\[Alpha]\[Beta]=-24.  *)
Levicivita\[Epsilon]/:Levicivita\[Epsilon][var__]*Levicivita\[Epsilon][var__]/;!Or@@(NumericQ[#]&/@Flatten[{var}]):= LCsign Length[{var}]!
Levicivita\[Epsilon]/:Power[Levicivita\[Epsilon][var__?(FreeQ[#,_Number]&)],2]:=LCsign Length[{var}]!;
(*the typical case*)
Levicivita\[Epsilon]/:Levicivita\[Epsilon][var1__] Levicivita\[Epsilon][var2__]:=Module[{commonIndices,rest1,rest2,s1,s2,ex,from},
(*the indices both have*)
commonIndices=Intersection@@(Select[#,Function[y,!NumberQ[y]]]&/@{{var1},{var2}});
(*the indices that exist only once*)
rest1=Complement[{var1},commonIndices];
rest2=Complement[{var2},commonIndices];
(*reordering indices and keep track of sign changes*)s1=Signature[{var1}]/Signature[Join[commonIndices,rest1]];
s2=Signature[{var2}]/Signature[Join[commonIndices,rest2]];
(*the new indices pairs*)ex=({rest1,#,Signature[#]}&/@Permutations[rest2])/Signature[rest2];
(*make Kronecker symbols*)from=Plus@@Apply[Times,{#[[3]],Thread[KroneckerDelta[#[[1]],#[[2]]]]}&/@ex,2];
LCsign Length[commonIndices]! s1 s2 from]

(* Antisymmetric. Because of this, one should notice the order of the arguments of Lecivita\[Epsilon] even in pattern, otherwise it might not work!! *)
(* Levicivita\[Epsilon][i__]/;Signature[List[i]]===-1:=-Levicivita\[Epsilon][Sequence@@Sort[{i}]] *)
Levicivita\[Epsilon][i__]/;!OrderedQ[List[i]]:=With[{list={i}},Signature[list]* Levicivita\[Epsilon][Sequence@@Sort[list]]]

Levicivita\[Epsilon][i__]/;Signature[List[i]]===0 =0;



(* Sum over polarizations *)
(* with the same momenta *)
polarization/:polarization[p_,\[Mu]_Symbol] polarization[p_,\[Nu]_Symbol]:=If[$NonRelativistic==False,-Metric[\[Mu],\[Nu]]+(momentum[p,\[Mu]] momentum[p,\[Nu]])/M[p]^2,
KroneckerDelta[\[Mu],\[Nu]]]
polarization/:polarization[p_,\[Mu]_Symbol] sp[polarization[p_],momentum[k_]]:=If[$NonRelativistic==False,
-momentum[k,\[Mu]]+(momentum[p,\[Mu]] sp[momentum[p],momentum[k]])/M[p]^2,
momentum[k,\[Mu]]/.momentum[polarization[l_],i_]:>polarization[l,i]]
sp/:sp[polarization[p_],v1_] sp[polarization[p_],v2_]/;((v1=!=polarization[p])&&(v2=!=polarization[p])):=If[$NonRelativistic==False,
-sp[v1,v2]+(sp[momentum[p],v1] sp[momentum[p],v2])/M[p]^2,
sp[v1,v2]]

(* momenta with different signs *)
polarization/:polarization[p_,\[Mu]_Symbol] polarization[q_,\[Nu]_Symbol]/;(q===-p):=If[$NonRelativistic==False,-Metric[\[Mu],\[Nu]]+(momentum[p,\[Mu]] momentum[p,\[Nu]])/M[p]^2,
KroneckerDelta[\[Mu],\[Nu]]]
polarization/:polarization[p_,\[Mu]_Symbol] sp[polarization[q_],momentum[k_]]/;(q===-p):=If[$NonRelativistic==False,
-momentum[k,\[Mu]]+(momentum[p,\[Mu]] sp[momentum[p],momentum[k]])/M[p]^2,
momentum[k,\[Mu]]/.momentum[polarization[l_],i_]:>polarization[l,i]]
sp/:sp[polarization[p_],v1_] sp[polarization[q_],v2_]/;((q===-p)&&(v1=!=polarization[p])&&(v2=!=polarization[p])):=If[$NonRelativistic==False,
-sp[v1,v2]+(sp[momentum[p],v1] sp[momentum[p],v2])/M[p]^2,
sp[v1,v2]]

polarization/:polarization[q_,i1_Symbol,j1_Symbol]polarization[p_,i2_Symbol,j2_Symbol]/;(q===-p):=polarizationSum[i1,j1,i2,j2,M[p],p]

(* polarization sum of a vector field *)
polarizationSum[\[Mu]_Symbol,\[Nu]_Symbol,M_,p_]:=If[$NonRelativistic==False,-Metric[\[Mu],\[Nu]]+(momentum[p,\[Mu]] momentum[p,\[Nu]])/M^2 ,
KroneckerDelta[\[Mu],\[Nu]]]
(* polarization sum of a tensor field *)
polarizationSum[\[Mu]_Symbol,\[Nu]_Symbol,\[Rho]_Symbol,\[Sigma]_Symbol,M_,p_]:=1/2 (polarizationSum[\[Mu],\[Rho],M,p] polarizationSum[\[Nu],\[Sigma],M,p]+
polarizationSum[\[Mu],\[Sigma],M ,p]polarizationSum[\[Nu],\[Rho],M,p])- 1/3 polarizationSum[\[Mu],\[Nu],M,p] polarizationSum[\[Rho],\[Sigma],M,p]


(* ::Subsection::Closed:: *)
(*Including fermions*)


(* ::Input:: *)
(*(* General idea on the codes for fermions:*)
(*Define a function Bar, and use it to indicate the outgoing fermions, both for the field and for the spinor.*)
(*This means, if the wave function WaveFun[\[Psi]] = u, then  WaveFun[Bar[\[Psi]]] = Bar[u].*)
(*Use Operate to apply Bar to the fermions, which gives  Operate[Bar, \[Psi][i,j]] = Bar[\[Psi]][i,j]. *)*)


GM=GammaMatrix;

BOctet:={{Sigma0/Sqrt[2]+Lambda/Sqrt[6],Sigmap,Proton},{Sigmam,-(Sigma0/Sqrt[2])+Lambda/Sqrt[6],Neutron},{Xim,Xi0,-2/Sqrt[6] Lambda}}

(*
FermionQ[f_]:=MemberQ[Fermionlist,f]
(*FieldQ[f_Symbol?FermionQ]:=True*)
FermionQ[x_?NumericQ]:=False
*)
FermionQ[_]:=False
(FermionQ[#] := True) &/@Evaluate[Fermionlist]
(FermionQ[Bar@#] := True) &/@Evaluate[Fermionlist]


(* Using Bar to define Bar[\[Psi]]=Overscript[\[Psi], _]=\[Psi]^\[Dagger] \[Gamma]^0, not to mean the antiparticle *)

(* For Bar[a+b]=Bar[a]+Bar[b] *)
(* Bar[x_Plus]:=Plus@@(Bar[#]&/@List@@x) *)
(* a:Bar[x_Plus]:= (Clear[aux]; Block[{aux=True},Thread[a,Plus]]/;!TrueQ[aux]) *)
a:Bar[x_Plus]:=Thread[Unevaluated@a,Plus]
Bar[a_?NumericQ f_]:=a Bar[f]

(*
FermionQ[Bar[f_]]:=MemberQ[Fermionlist,f]
(*FieldQ[Bar[f_Symbol?FermionQ]]:=True*)
*)

(* FieldList=UnsortedUnion[FieldList,Fermionlist,Bar[Fermionlist]]; *)

NonCommutativeList=Join[{GammaMatrix, Diracsigma, Paulisigma, SpinorU, SpinorV, List}, Fermionlist];

MoreFermion[a__]:=Module[{alis,app},alis=Flatten[{a}];
app=AppendTo[Fermionlist,#]&/@alis;
(FermionQ[#]=True)&/@alis;
(FieldQ[#]=True)&/@alis;
(*Refresh FieldList
FieldList=UnsortedUnion[FieldList,alis,Bar[alis]];*)
(*Refresh NonCommutativeList*)
NonCommutativeList=UnsortedUnion[NonCommutativeList,alis];
(*Print["Fermion fields include:"];*)
Fermionlist=UnsortedUnion@app[[-1]]
]


(* SpinorDot *)
(* Define product in spinor space as a \[CenterDot] center dot *)
CommutativeQ[x_]:= And@@(FreeQ[NonCommutativeList,#]&/@Level[x,{-1},Heads->True])
NonCommutativeQ[x_]:= Or@@(MemberQ[NonCommutativeList,#]&/@Level[x,{-1},Heads->True])

(* It is very subtle to define the operations with attribute Flat *)

SpinorDot[a_List]:=a

SetAttributes[SpinorDot,{Flat,OneIdentity}]
CenterDot=SpinorDot;

SpinorDot[x_,1] := x
SpinorDot[1,x_] := x

(* Needed, otherwise infinite iteration due to sd[1] *)
SpinorDot[s1___:1,1,s2___:1] := Unevaluated@SpinorDot[s1, s2] /.
(* Needed for replacing SpinorDot[] by 1. One can NOT define SpinorDot[]=1 for the Flat attribute *)
SpinorDot[]->1
(* In the following, . in b_. is important, which uses the fact that Times has the attribute OneIdentity *)
SpinorDot[s1___,c_ b_.,s2___]:=c SpinorDot[s1,b,s2] /;(CommutativeQ[c])

(* for expanding the expression *)
e: SpinorDot[p1___, p2_Plus, p3___] := Distribute[Unevaluated[e]]

(* For matrices in other space, e.g. the flavor space *)
SpinorDot[a_,b_List]:=SpinorDot[a,#]&/@b/;!MatchQ[List,Head[a]]
SpinorDot[b_List,a_]:=SpinorDot[#,a]&/@b/;!MatchQ[List,Head[a]]
SpinorDot[a_List,b_List]:=Inner[SpinorDot,a,b]



(* Define the wave function for a fermion field *)
WaveFun[f_Symbol?FermionQ,p___]:=SpinorU[p]
WaveFun[f_Symbol?FermionQ[i__],p___]:=SpinorU[p][i]

WaveFun[Bar[f_?FermionQ],p___]:=Bar[SpinorU][p]
WaveFun[Bar[f_?FermionQ][i__],p___]:=Bar[SpinorU][p][i]


Protect[$Index];
(* Attach each of m a pair of indices *)
ToComponent[m__]:=Module[{mlis,l,itab},mlis={m};
l=Length[mlis];
(* Make a table of indices *)
itab=Partition[Table[Unique[ToString[$Index]],{l+1}],2,1];
(* (* For fermion fields, change the first and last indices to 1 *)
itab= If[FermionQ[mlis[[1]]],ReplacePart[itab,{{1,1},{l,2}}->1],itab];*)
(* Attach the indices to each matrix *)
(* Times@@MapThread[Indices,{mlis,itab}] *)
Times@@Table[mlis[[i]][Sequence@@itab[[i]]],{i,l}]/.(* Moving indices to inside pd *)
pd[f_?FieldQ,\[Mu]__][i_,j_]/;MemberQ[Flatten@itab,i]:>pd[f[i,j],\[Mu]]
]
(* Replace SpinorDot by ToComponent *)
SpinorDotToComponent[exp__]:=exp/.SpinorDot->ToComponent

(* Components to matrices *)
ToSpinorDot[x_Times]:=Module[{l,l1,l2,strin},l=List@@x; strin=ToString[$Index];
(* those which are not spinors or dirac matrices *)
l1=Select[l,StringFreeQ[ToString[#1],strin]&];
(* those with components. One should be careful with the ordering here,
since, e.g. Sort[{$Index9,$Index10}] = {{$Index10,$Index9}} *)
l2=Sort[Complement[l,l1],OrderedQ[Map[ToExpression@StringDrop[ToString@#,StringLength[strin]]&,{#1[[1]],#2[[1]]}]]&];
(* to SpinorDot *)
Times@@l1 *SpinorDot@@(Head[#1]&)/@l2]

ToSpinorDot[0]:=0


(* ::Subsection:: *)
(*Deriving the amplitude*)


(* This function counts number of derivatives in a given term *)
pdCount[exp_ /; (MemberQ[{Times, Power}, Head[exp]])] :=
 Count[exp /.
   (* Take into account terms like \!\(
\*SubscriptBox[\(\[PartialD]\), \(\[Mu]\)]\[Phi]\)\[PartialD]^\[Mu]\[Phi] *)
   {pd[a_, b___]^2 :> Hold[pd[a, b] pd[a, b]]},
   pd[_, __],
   (* at level -1 *)-1]

pdCount[exp_] :=
 Print["pdCount::Head of the term is neither Times nor Power."]

(* This function picks out arguments of pd[\[Phi],\[Mu]].
For i=0(1), it forms a list of fields keeping (having deleted) Lorentz indices, being acted on by derivatives.
For i=2, it forms a list of the Lorentz indeices.
For i=3, gives a list of the Lorentz-index lists of vector and tensor fields *)

pdPick[exp_,0]:=#[[1]]&/@Cases[Flatten[{exp}/.{Times->List,SpinorDot->List,Power[pd[a_,\[Mu]___],2]:>List[ pd[a,\[Mu]],pd[a,\[Mu]] ],
(* replace pd[pd[\[Phi],\[Mu]],\[Nu]] by pd[\[Phi],\[Mu]] *)
pd[pd[a_,\[Mu]_],\[Nu]_]:> pd[a,\[Mu]]}],pd[_,___]]

(* delete the Lorentz indices of vector and tensor mesons *)
pdPick[exp_,1]:=pdPick[exp,0]/.b_?FieldQ[i__]:>b

(* Double derivative terms:
One possible way to take into account the double or even more derivative terms is follows:
Since pdPick is only used to get the field content, and one Lorentz index of derivative
acting on that field, so one may discard the second derivative in the definition of pdPick,
which means replace pd[pd[\[Phi],\[Mu]],\[Nu]] by pd[\[Phi],\[Mu]] in pdPick. Then in the function MomentumProduct,
pd[\[Phi],\[Mu]] will be replaced by Subscript[p, \[Mu]], where p is the momentum of \[Phi]. The next step is
to find momentum p, and replace Subscript[p, \[Mu]+\[Nu]] by Subscript[p, \[Mu]] Subscript[p, \[Nu]].  *)

(*
seq[n_]:=Sequence@@Table[1,{n}]
(* For multiple derivative, this gives the Lorentz index as \[Mu]+\[Nu]+... *)
pdPick[exp_,2]:=Sum[#[[seq[i],2]],{i,0,Depth[#]-2}]&/@Cases[Flatten[{exp}/.{Times->List,
Power[pd[a_,\[Mu]___],2]:>List[ pd[a,\[Mu]],pd[a,\[Mu]] ],Power[pd[pd[a_,\[Mu]_],\[Nu]_],2]:>List[pd[pd[a,\[Mu]],\[Nu]],pd[pd[a,\[Mu]],\[Nu]]]}],pd[_,___]]
*)

pd[pd[a_,\[Mu]_],\[Nu]_]:=pd[a,Sequence@@Sort[{\[Mu],\[Nu]}]]
pd[pd[pd[a_,\[Mu]_],\[Nu]_],\[Rho]_]:=pd[a,Sequence@@Sort[{\[Mu],\[Nu],\[Rho]}]]

(* Auxilliary function *)
dp[\[Mu]_]:=\[Mu]
(* For multiple derivative, this gives the Lorentz index as dp[\[Mu],\[Nu],...] *)
pdPick[exp_,2]:=dp[Sequence@@Rest[#]]&/@(Cases[Flatten[{exp}/.{Times->List,SpinorDot->List,
Power[pd[a_,\[Mu]___],2]:>List[ pd[a,\[Mu]],pd[a,\[Mu]] ],
Power[pd[pd[a_,\[Mu]_],\[Nu]_],2]:>List[pd[pd[a,\[Mu]],\[Nu]],pd[pd[a,\[Mu]],\[Nu]]]}],
pd[_,___]]/.pd->List)

(* This gives the Lorentz indices of vector and tensor fields *)
pdPick[exp_,3]:=Which[Depth[#[[1]]]===1,{},
Depth[#[[1]]]===2,Apply[List,#[[1]]]
]&/@(Cases[Flatten[{exp}/.{Times->List,SpinorDot->List,
Power[pd[a_,\[Mu]___],2]:>List[ pd[a,\[Mu]],pd[a,\[Mu]] ],
Power[pd[pd[a_,\[Mu]_],\[Nu]_],2]:>List[pd[pd[a,\[Mu]],\[Nu]],pd[pd[a,\[Mu]],\[Nu]]]}],
pd[_,___]]/.pd->List)

(* The rest part of a term besides the partial derivatives including the fields and coeffecients *)
pdRest[exp_]:=DeleteCases[DeleteCases[exp,pd[_,___]],pd[_,___]^_]

(* Gives the coefficient in a Lagrangian apart from fields and their derivatives *)
coefficient[exp_]:=pdRest[exp]/.{a_?FieldQ[\[Mu]__]->1,a_?scalarQ->1}

(* nonpdPick[exp] returns a list of fields which are not acted on by \[PartialD]. (\[Phi]^n) gives a n times \[Phi] in the list. *)
nonpdPick[exp_]:=Select[Flatten[{exp}/.
(* delete the Lorentz indices of vector and tensor mesons. Times->List must be here, otherwise
1) it would give Subscript[\[Epsilon], \[Mu]\[Nu]\[Alpha]\[Beta]]\[PartialD]^\[Mu]A^\[Nu]\[PartialD]^\[Alpha]A^\[Beta]->Subscript[\[Epsilon], \[Mu]\[Nu]\[Alpha]\[Beta]]\[PartialD]^\[Mu]A\[PartialD]^\[Alpha]A=0;
2) it might get different order from the one by nonpdPick0. E.g.,
pi0 Kstar[\[Mu]] in nonpdPick0 would be {pi0,Kstar[\[Mu]]}, and here it should then be {pi0, Kstar}.
However, if one applies Times->List after replacing Kstar[\[Mu]] by Kstar, then it would result
in {Kstar,pi0} since after removing [\[Mu]], the cononical order has been changed from pi0 Kstar[\[Mu]] to Kstar pi0. *)
{Times->List,SpinorDot->List,b_?FieldQ[i__]:>b}/.{a_?(!constantQ[#]&)^n_:>Table[a,{n}]}],FieldQ]

(* nonpdPick0[exp] returns a list of fields, with Lorentz indices kept,
which are not acted on by \[PartialD]. (\[Phi]^n) gives a n times \[Phi] in the list. *)
nonpdPick0[exp_]:=Select[Flatten[{exp}/.{a_?(!constantQ[#]&)^n_:>Table[a,{n}],Times->List,SpinorDot->List}],
FieldQ[#]\[Or]FieldQ[Head[#]]&]

(* This function returns a list of the positions of the element el in a list,
and el is included as the last element of the formed list. *)
(* Level 1 in Position should be specified in order to distinguish, e.g. Neutron and Bar[Neutron].
Otherwise, Neutron in Bar[Neutron] would also be counted *)
position[list_,el_]:=Flatten@{Position[#1,#2,1],#2}&[list,el]
(* Manipulate the particle list, give a table with each row being a list consisting
the positions and name of a particle (name is the last element of the list). *)
Relist[list_]:=Union@Table[position[#,#[[i]]],{i,Length[#]}]&[list]


(* Select the part relevant for a certain process from a given Lagrangian Lag.
The particles in the process should be collected in list1. If the particle appear n times,
list1 should contain n copies of the particle name. *)
(* For instance,
      \[Pi]^+ \[Pi]^-->\[Pi]^+ \[Pi]^-,  LagrangianPart[Lag,{pip,pim,pip,pim}]  *)
(* LagrangianPart0[Lag_,list1_]:=With[{others = Complement[FieldList, list1]},
	Lag/.a_?(MemberQ[others, #] &)->0 /.{0[i__]->0}] *)
LagrangianPart0[Lag_,list1_]:=With[{others=Complement[FieldList,list1]},
Lag/.Flatten[{Rule[#,0]&/@others,
(* If there is a fermion Bar[f], but no f, in list1, then Bar[f] will be kept *)
MapThread[Rule,{list1,list1}]}] /. {0[i__]->0}]

(*
LagrangianPart[Lag_,list1_List]:=Module[{r1,r2,r3,r4},r1=LagrangianPart0[Lag,list1];
r2=Expand[Normal[r1]];If[Head[r2]===Plus,r3=List@@r2,r3={r2}];
(* Compare the fields in each term with list1 *)
r4=(Sort[Join[pdPick[#,1],nonpdPick[#]]]===Sort@list1) #&/@r3/.{True->1,False->0};
r4/.List->Plus
]
*)

(* better method, also works for fermions, 20.02.2013 *)
LagrangianPart[Lag_,list1_List]:=Module[{la,sel,la2,r3,r4},
sel[l_,e_]:=Select[l,!FreeQ[#,e]&];
la=Expand@LagrangianPart0[Lag,list1];
If[Head[la]===Plus,la2=List@@la,la2={la}];
r3=Fold[sel,la2,Union@list1]/.Select[___]:>0//Quiet;
r4=(Sort[Join[pdPick[#,1],nonpdPick[#]]]===Sort@list1) #&/@r3/.{True->1,False->0};
r4/.List->Plus
]

(* NGB[exp_,i_Integer]:=Expand[1/Fpi^i Coefficient[exp,Power[Fpi,-i]]] *)
NGB[exp_,0]:=exp/.a_?GBQ->0
NGB[exp_,i_Integer]:=Module[{gbtag,ltagged},
   constantQ[gbtag]=True;
   ltagged=exp/.{a_?GBQ:>a gbtag};
   Coefficient[ltagged,gbtag^i] ]

(* Wave functions *)
SetAttributes[WaveFun,Listable]
WaveFun[f_?scalarQ,p___]:=1
WaveFun[f_?vectorQ[\[Mu]__],p_]:=polarization[p,\[Mu]]
WaveFun[f_?tensorQ[\[Mu]__],p_]:=polarization[p,\[Mu]]


(* Select the column containing el from relist of particles *)
select[particles_,el_]:=Flatten@Select[Relist[particles],MemberQ[#,el]&]

myOuter[f_,a__]:=Outer[f,a]
myOuter[f_]:={1}

(* Product of wave fucntions of fields without derivatives *)
WaveProduct[exp_,particles_,plist_]:=Module[{f,positions,r1},
(* Get the positions of the fields without \[PartialD] in the whole list of particles. This forms a matrix
with each row corresponding to a field without \[PartialD]. n copies of identical particles results in n rows. *)
positions=Most[#]&/@(select[particles,#]&/@nonpdPick[exp]);
r1=DeleteCases[ (* using an auxiliary function f *)
Flatten[  myOuter[f,Sequence@@
(* Delete wave functions of spin-0 particles. *)
DeleteCases[WaveFun[nonpdPick0[exp],momentum[plist[[#]]]&/@positions],{1..}]]  ]
(* Delete terms with the same momentum which should not be present *)
/.f[___,polarization[p_,\[Mu]__],___,polarization[p_,\[Nu]__],___]->0
(* Delete 0 from the list *)
,0];
1/Length[#] Plus@@#&[r1]/.{f->Times}]


(* No matter whether the fields with \[PartialD] are identical or not *)
(* This function forms a sum of the product of different momenta. E.g.,
p1/3 (p2+p3)/2 + p2/3 (p1+p3)/2 + p3/3 (p1+p2)/2 = 1/6 (p1 p2 + p1 p3 + p2 p1 + p2 p3 + p3 p1 + p3 p2) *)
(* Wave function product is also included if the Lagrangian has derivative. -- 11.05.2011 *)
MomentumProduct[exp_,particles_,plist_,OptionsPattern[]]:=Module[{ifac,f,g,positions,nopositions,pout,wout,r1,holdplist},
If[OptionValue[NonRelativistic]==False,ifac=-I,
(* For NonRelativistic case,\[PartialD]^ishould still be -I p^i,since the minus sign due to  (g^ij )
has been taken into account in the nonrelativistic Lagrangian! *)
ifac=-I];
(* positions gets the positions of the fields with \[PartialD] in the whole list of particles.
This forms a matrix with each row corresponding to a field with \[PartialD].
n copies of identical particles results in n rows. *)
positions=Most[#]&/@(select[particles,#]&/@pdPick[exp,1]);
(* nopositions is for fields without \[PartialD] *)
nopositions=Most[#]&/@(select[particles,#]&/@nonpdPick[exp]);
(* Hold is necessary for geting correct pd[pd[_,_],_], otherwise
momentum[-p,dp[a,b]]/.momentum[p_,dp[a_,b_]]:>momentum[p,a] momentum[p,b]
would give -p^a p^b, not the correct (-p^a)(-p^b) = p^a (p^b). *)
holdplist=Hold[#]&/@plist;
pout=Outer[f,Sequence@@(momentum[holdplist[[#]]]&/@positions)];
wout=myOuter[g,Sequence@@
(* Delete wave functions of spin-0 particles. *)
DeleteCases[WaveFun[nonpdPick0[exp],momentum[plist[[#]]]&/@nopositions],{1..}]];
r1=DeleteCases[
Flatten@Outer[Times,pout,wout]/.{
(* Delete terms with the same momentum which should not be present *)
f[___,a_,___,a_,___]->0,
f[___,momentum[Hold[p_]],___] g[___,polarization[p_,_],___]->0,
g[___,polarization[p_,\[Mu]__],___,polarization[p_,\[Nu]__],___]->0 }
(* Attach Lorentz indices to momenta. Times ifac to each p so that \[PartialD]^\[Mu] is replaced by ifac p^\[Mu] *)
(*/.f[pp__]:>f[Sequence@@momentum[ifac {pp},pdPick[exp,2]]]*)
/.f[pp__]:>f[Sequence@@(
momentum[ifac {pp},pdPick[exp,2]]
(* Multiplying by wave functions *)
* WaveFun[pdPick[exp,0],{pp}])]
(* Delete 0 from the list *)
,0];
1/Length[#] Plus@@#&[r1]/.{f->Times,g->Times,momentum[momentum[a_],b_]:>momentum[a,b]}
(* Repalce properly multiple derivatives by momenta *)
/.{momentum[p_,dp[\[Mu]_,\[Nu]_]]:>ifac momentum[p,\[Mu]] momentum[p,\[Nu]],
(* Triple derivatives still needs to be checked *)
momentum[p_,dp[a_,b_,c_]]:>-momentum[p,a]momentum[p,b]momentum[p,c]}]//ReleaseHold


(* Without symmetric factor which will be considered in function TreeAmplitude using sfactor[list],
see below. This function returns the amplitude in momentum space for a term of Lagrangian *)
aPiece[exp_,particles_,momenta_]:=If[(* If the particle list given by particles matches the fields
appearing in the Lagrangian term, then evaluate *)
Sort@Join[pdPick[exp,1],nonpdPick[exp]]===Sort@particles,
If[pdCount[exp]===0,
(* If there is no derivative, then it's easy *)
coefficient[#]*WaveProduct[#,particles,momenta]&[exp] ,
(* If there are derivatives, then run the following *)
coefficient[#]* MomentumProduct[#,particles,momenta]&[exp]]
,Print["aPiece:: Warning: The particle lists don't match!"]
]

(* sfactor calculates symmetric factor for given particles in list *)
sfactor[list_]:=Times@@Factorial[Last[#]&/@Tally[list]]

(* This function calculates the tree-level amplitudes (Feynman rules) given a Lagrangian lag.
Note that the function corresponds to the matrix element of -\[ScriptCapitalH] or \[ScriptCapitalL].
A phase of -1 or -I might need be multiplied for a specific purpose.
The particles involving in the considered process should be given in the list particles,
and their corresponding momentum are collected in the list momenta.
Attention should be paid to assigning incoming or outgoing to a field. The function replaces any \[PartialD] by -I p. *)
(* Symmetric factor is taken into account here! *)
(* TreeAmplitude[\[ScriptCapitalL],{in1,in2,anti-out3,anti-out4},{p1,p2,p3,p4}] gives amplitude for the process
in1(p1) + in2(p2) -> out3(-p3) + out4(-p4) *)

(* (* ***** Original version for bosons ***** *)
TreeAmplitude[lag_,particles_,momenta_]:=Module[{lagpart},
(* Pick out the relevant part, whose field content is identical to particles, from the Lagrangian *)
lagpart=LagrangianPart[lag,particles];
Which[(* If there are more than one terms *)
Head[Expand@lagpart]===Plus,
sfactor[particles]*Plus@@(aPiece[#,particles,momenta]&/@(List@@Expand[lagpart])),
(* If there is only one terms *)
Head[Expand@lagpart]===Times \[Or] Head[Expand@lagpart]===Power,
sfactor[particles]*aPiece[lagpart,particles,momenta],
(* If the Lagrangian is 0, then the amplitude is 0, too. *)
lagpart===0, 0
]
] *)

TreeAmplitude[lag_,particles_,momenta_]:=Module[{lag1,lagpart,aPiecef},
(* Pick out the relevant part, whose field content is identical to particles, from the Lagrangian *)
lagpart=LagrangianPart[lag,particles];
If[FreeQ[particles,_?FermionQ],lag1=lagpart;aPiecef=aPiece,
(* If there are fermions *)
lag1=SpinorDotToComponent[lagpart];
aPiecef[exp_,plist_,mlist_]:=With[{piece=Expand@aPiece[exp,plist,mlist]},
(* If identical particles are acted on by \[PartialD], then aPiece does not give a single term *)
If[Head[piece]===Plus,ToSpinorDot[#]&/@piece,ToSpinorDot@piece]]
];
(**)
With[ {ex=(*Expand@*)lag1},
Which[(* If there are more than one terms *)
Head[ex]===Plus,
sfactor[particles]*(aPiecef[#,particles,momenta]&/@ex),
(* If there is only one terms *)
Head[ex]===Times \[Or] Head[ex]===Power,
sfactor[particles]*aPiecef[lag1,particles,momenta],
(* If the Lagrangian is 0, then the amplitude is 0, too. *)
lag1===0, 0
] ]
]

(* the S-matrix element *)
SMatrixElement[x___]:=I TreeAmplitude[x]


(* For fermions, take the relevant part of the Lagrangian, NOT to be used in TreeAmplitude *)
FermionLagrangianPart[lag_,plist_]:=If[FreeQ[plist,_?FermionQ],
(* If there are no fermions *)
LagrangianPart[lag,plist],
(* If there are fermions. LagrangianPart as defined should give the expanded expression. *)
Module[{lc},lc=LagrangianPart[SpinorDotToComponent@lag,plist];
If[Head[lc]===Plus,ToSpinorDot[#]&/@lc,ToSpinorDot[lc]]
] ]



(* ::Section::Closed:: *)
(*Lagrangians for meson CHPT without external fields*)


(* ::Subsection:: *)
(*Building blocks and some replacing rules*)


(* Goldstone bosons. U and U^\[Dagger] are expanded in terms of \[CapitalPhi]. The default value for number of \[CapitalPhi] is 2.
It can be changed by using for instance U[\[CapitalPhi],n->3].  *)
UseriesOption=n->4;
Options[U]={UseriesOption};
Options[Udag]={UseriesOption};
Options[u]={UseriesOption};
Options[udag]={UseriesOption};
U[P_,OptionsPattern[]]:=IdentityMatrix[Length[P]]+Sum[(I Sqrt[2]/F0)^i 1/i! MatrixPower[P,i],{i,OptionValue[n]}]
Udag[P_,OptionsPattern[]]:=IdentityMatrix[Length[P]]+Sum[(-I Sqrt[2]/F0)^i 1/i! MatrixPower[P,i],{i,OptionValue[n]}]
u[P_,OptionsPattern[]]:=IdentityMatrix[Length[P]]+Sum[(I 1/(Sqrt[2] F0))^i 1/i! MatrixPower[P,i],{i,OptionValue[n]}]
udag[P_,OptionsPattern[]]:=IdentityMatrix[Length[P]]+Sum[(-I 1/(Sqrt[2] F0))^i 1/i! MatrixPower[P,i],{i,OptionValue[n]}]
Protect[n];
quarkMassMatrix:=If[$IsospinSymmetry==False,DiagonalMatrix[{mq[u],mq[d],mq[s]}], DiagonalMatrix[{mhat,mhat,mq[s]}]]
\[Chi]:=2 B0 quarkMassMatrix;
\[Chi]dag:=2 B0 quarkMassMatrix;


\[CapitalPhi]={{pi0/Sqrt[2]+eta/Sqrt[6],pip,Kp},
{pim,-(pi0/Sqrt[2])+eta/Sqrt[6],K0},
{Km,K0bar,-2 eta/Sqrt[6]}};
(* Standard mixing between \[Eta] and \[Eta]' *)
\[CapitalPhi]nonet={{pi0/Sqrt[2]+eta/Sqrt[3]+etap/Sqrt[6],pip,Kp},
{pim,-(pi0/Sqrt[2])+eta/Sqrt[3]+etap/Sqrt[6],K0},
{Km,K0bar,-(eta/Sqrt[3])+(2 etap)/Sqrt[6]}};
(* Expressing in term of eta0 and eta8, eta->1/3 eta0+2 Sqrt[2]/3 eta8,etap->-(1/3)eta8+2 Sqrt[2]/3 eta0 *)
\[CapitalPhi]nonet08={{eta0/Sqrt[3]+eta8/Sqrt[6]+pi0/Sqrt[2],pip,Kp},
{pim,eta0/Sqrt[3]+eta8/Sqrt[6]-pi0/Sqrt[2],K0},
{Km,K0bar,(eta0-Sqrt[2] eta8)/Sqrt[3]}};
(* Ideal mixing between \[Omega] and \[Phi] *)
Vnonet={{rho0/Sqrt[2]+omega/Sqrt[2],rhop,Kstarp},
{rhom,-(rho0/Sqrt[2])+omega/Sqrt[2],Kstar0},
{Kstarm,Kstar0bar,phi}};
(* Ideal mixing between Subscript[f, 2] and Subscript[f, 2]' *)
Tnonet={{a20/Sqrt[2]+f2/Sqrt[2],a2p,K2p},
{a2m,-(a20/Sqrt[2])+f2/Sqrt[2],K20},
{K2m,K20bar,f2p}};
Q=DiagonalMatrix[{2/3,-(1/3),-(1/3)}];


commutator[a_,b_]:=a.b-b.a
Anticommutator[a_,b_]:=a.b+b.a


(* Replace Subscript[p, i]\[CenterDot]Subscript[p, j] by Mandelstam variables. u should not be confused with the chiral field u[P] in the above *)
(* Note the definition, all momenta are incoming. It might need to be redefined *)
MandelstamRules={sp[p1,p2]->1/2 (s-sp[p1,p1]-sp[p2,p2]),
sp[p3,p4]->1/2 (s-sp[p3,p3]-sp[p4,p4]),
sp[p1,p3]->1/2 (t-sp[p1,p1]-sp[p3,p3]),
sp[p2,p4]->1/2 (t-sp[p2,p2]-sp[p4,p4]),
sp[p1,p4]->1/2 (u-sp[p1,p1]-sp[p4,p4]),
sp[p2,p3]->1/2 (u-sp[p2,p2]-sp[p3,p3]),
sp[p1+p2,p1+p2]->s, sp[p3+p4,p3+p4]->s,
sp[p1+p3,p1+p3]->t, sp[p2+p4,p2+p4]->t,
sp[p1+p4,p1+p4]->u, sp[p2+p3,p2+p3]->u};

(* redefine: p1,p2 are incoming, and p3,p4 are outgoing *)
MandelstamRules2={sp[p1,p2]->1/2 (s-sp[p1,p1]-sp[p2,p2]),
sp[p3,p4]->1/2 (s-sp[p3,p3]-sp[p4,p4]),
sp[p1,p3]->-(1/2) (t-sp[p1,p1]-sp[p3,p3]),
sp[p2,p4]->-(1/2) (t-sp[p2,p2]-sp[p4,p4]),
sp[p1,p4]->-(1/2) (u-sp[p1,p1]-sp[p4,p4]),
sp[p2,p3]->-(1/2) (u-sp[p2,p2]-sp[p3,p3]),
sp[p1+p2,p1+p2]->s,sp[p3+p4,p3+p4]->s,
sp[p1-p3,p1-p3]->t,sp[p2-p4,p2-p4]->t,
sp[p1-p4,p1-p4]->u,sp[p2-p3,p2-p3]->u};

MandelstamRulesij={sp[p1,p2]->1/2 (s12-sp[p1,p1]-sp[p2,p2]),
sp[p3,p4]->1/2 (s34-sp[p3,p3]-sp[p4,p4]),
sp[p1,p3]->1/2 (s13-sp[p3,p3]-sp[p1,p1]),
sp[p2,p4]->1/2 (s24-sp[p2,p2]-sp[p4,p4]),
sp[p1,p4]->1/2 (s14-sp[p1,p1]-sp[p4,p4]),
sp[p2,p3]->1/2 (s23-sp[p2,p2]-sp[p3,p3]),
sp[p1+p2,p1+p2]->s12, sp[p3+p4,p3+p4]->s34,
sp[p1+p3,p1+p3]->s13, sp[p2+p4,p2+p4]->s24,
sp[p1+p4,p1+p4]->s14, sp[p2+p3,p2+p3]->s23};
onshellRules={sp[p1,p1]->m[1]^2,sp[p2,p2]->m[2]^2,sp[p3,p3]->m[3]^2,sp[p4,p4]->m[4]^2};

(* Gell-Mann-Okubo relations in case of isospin conservation *)
(* := should be used for GMORules and GMORulesIB *)
GMORules:={mq[s]->1/B0 (M[K]^2-1/2 M[pi]^2),mq[d]->1/(2 B0) M[pi]^2, mq[u]->1/(2 B0) M[pi]^2,mhat->1/(2 B0) M[pi0]^2};
GMORules2={mq[s]->(3 M[eta]^2-M[pi0]^2)/(4 B0),mhat->1/(2 B0) M[pi0]^2};
(* Gell-Mann-Okubo relations in case of isospin breaking, mhat=1/2 (mu+md), \[Delta]m=md-mu *)
GMORulesIB:={mq[s]->1/B0 M[K0]^2- mq[d],mq[u]->2 mhat-mq[d],mhat->1/(2 B0) M[pi]^2,mq[d]->mhat+1/2 \[Delta]m};


(* ::Subsection:: *)
(*Lagrangians*)


Options[LMchpt]={UseriesOption};
(* \[ScriptCapitalO](p^2) *)
LMchpt[\[CapitalPhi]_,OptionsPattern[]][2]:=F0^2/4 Tr[pd[U[\[CapitalPhi],n->#],\[Mu]].pd[Udag[\[CapitalPhi],n->#],\[Mu]]]+F0^2/4 Tr[\[Chi].Udag[\[CapitalPhi],n->#]+U[\[CapitalPhi],n->#].\[Chi]dag]&[OptionValue[n]]
(* \[ScriptCapitalO](p^4) *)
LMchpt[\[CapitalPhi]_,OptionsPattern[]][4]:=Module[{\[Mu],\[Nu]},
L[1] Tr[pd[Udag[\[CapitalPhi]],\[Mu]].pd[U[\[CapitalPhi]],\[Mu]]]Tr[pd[Udag[\[CapitalPhi]],\[Nu]].pd[U[\[CapitalPhi]],\[Nu]]]+
L[2] Tr[pd[Udag[\[CapitalPhi]],\[Mu]].pd[U[\[CapitalPhi]],\[Nu]]]Tr[pd[Udag[\[CapitalPhi]],\[Mu]].pd[U[\[CapitalPhi]],\[Nu]]]+
L[3] Tr[pd[Udag[\[CapitalPhi]],\[Mu]].pd[U[\[CapitalPhi]],\[Mu]].pd[Udag[\[CapitalPhi]],\[Nu]].pd[U[\[CapitalPhi]],\[Nu]]]+
L[4] Tr[pd[Udag[\[CapitalPhi]],\[Mu]].pd[U[\[CapitalPhi]],\[Mu]]]Tr[\[Chi]dag.U[\[CapitalPhi]]+\[Chi].Udag[\[CapitalPhi]]]+
L[5] Tr[pd[Udag[\[CapitalPhi]],\[Mu]].pd[U[\[CapitalPhi]],\[Mu]].(\[Chi]dag.U[\[CapitalPhi]]+Udag[\[CapitalPhi]].\[Chi])]+
L[6] Tr[\[Chi]dag.U[\[CapitalPhi],n->#]+\[Chi].Udag[\[CapitalPhi],n->#]]^2+
L[7] Tr[\[Chi]dag.U[\[CapitalPhi],n->#]-\[Chi].Udag[\[CapitalPhi],n->#]]^2+
L[8] Tr[\[Chi]dag.U[\[CapitalPhi],n->#].\[Chi]dag.U[\[CapitalPhi],n->#]+\[Chi].Udag[\[CapitalPhi],n->#].\[Chi].Udag[\[CapitalPhi],n->#]]&[OptionValue[n]]
]

(* replace the Li's by their finite part plus infinity, here inf = 1/(32 \[Pi]^2)(2/(d-4)-[ln(4\[Pi]) +\[CapitalGamma]'(1)+1] ) *)
renormalized[e_,inf_] := Module[{Gam}, Gam={3/32, 3/16, 0, 1/8, 3/8, 11/144, 0, 5/48, 1/4, -1/4};
	e /.MapThread[Rule, {Table[L[i], {i, 1, 8}], Table[Lr[i] + Gam[[i]]*inf, {i, 1, 8}]}]
  ]

(* Wess-Zumino-Witten term for five Goldstone bosons *)
LWZW[\[Phi]_]:=(3 (Sqrt[2])^5)/(240 \[Pi]^2 F0^5) Levicivita\[Epsilon][\[Mu],\[Nu],\[Alpha],\[Beta]] Tr[#.pd[#,\[Mu]].pd[#,\[Nu]].pd[#,\[Alpha]].pd[#,\[Beta]]]&[\[Phi]]


(* ::Section:: *)
(*One-loop functions*)


(* ::Text:: *)
(*Non-relativistic functions have not been included yet.*)


(* count the power of a given momentum in a given term e *)
MomentumPower[e_,p_]:=Module[{e1,aux},
(* List must be changed to aux since Times is Listable *)
e1=e//.sp[p,q_]^n_:>aux@@Table[sp[p,q],{i,n}];
Count[e1,p,-1] ]


(* General formula for Feynman parameterization *)
FeynmanParameterization[p:{{_,_Integer:1}..},x_List]:=Module[
   {d,a,part2,as,denorm},
   part2[list_]:=If[Length[list]==1,1,list[[2]]];
   d=#[[1]]&/@p;
   a=part2[#]&/@p;
   as=Plus@@a;denorm=Plus@@(d x);
   Gamma[as]/Times@@Gamma[a] (DiracDelta[1-Plus@@x] Times@@(x^(a-1)))/(denorm)^as/.DiracDelta[0]->1
]

(* Feynman parameterization with the denominator transfered into a quadrtic form.
The last argument should be given as the loop momentum being integrated. *)
FeynmanParameterization[p:{{_,_Integer:1}..},x_List,l_]:=Module[
   {d,a,part2,as,de1,de2,de3},
   part2[list_]:=If[Length[list]==1,1,list[[2]]];
   (* list of denorminators of propagators *)
   d=#[[1]]&/@p;
   (* list of powers of propagators *)
   a=part2[#]&/@p;
   as=Plus@@a;
   de1=Plus@@(d x);
   de2=Coefficient[de1,l^2] (Simplify[l+Coefficient[de1,l]/(2 Coefficient[de1,l^2])])^2/.Plus@@x->1;
   (* de3=de2+Collect[(de1/.l->0)-(de2/.l->0),x[[1]],Simplify]; *)
   de3=de2+Collect[(de1/.l->0)-(de2/.l->0),#[[2,2,1]]&/@p[[All,1]],Simplify];
   Gamma[as]/Times@@Gamma[a] (DiracDelta[1-Plus@@x] Times@@(x^(a-1)))/(de3)^as/.{DiracDelta[0]->1}
]


(* ::Subsection:: *)
(*Tadpole*)


(* Repalcing rules *)
OnePointLoopRules2[l_,m_]:={(* l^2 *)
sp[l,l]:>m^2 LFA0[m^2],
(* Subscript[l, \[Mu]] Subscript[l, \[Nu]] *)
momentum[l,\[Mu]_] momentum[l,\[Nu]_]:>Metric[\[Mu],\[Nu]] LFA00[m^2],
(* Subscript[l, \[Mu]]l\[CenterDot]p *)
momentum[l,\[Mu]_] sp[l,p_?(UnsameQ[l,#]&)]:>momentum[p,\[Mu]] LFA00[m^2],
(* l\[CenterDot]Subscript[p, 1]l\[CenterDot]Subscript[p, 2 ] *)
sp[l,p1_?(UnsameQ[l,#]&)] sp[l,p2_?(UnsameQ[l,#]&)]:>sp[p1,p2] LFA00[m^2]}

(* selcting proper rules for one-point loops *)
OnePointLoopRulesSelecter[e_,l_,m_]:=
Which[MomentumPower[e,l]===0,e LFA0[m^2],
MomentumPower[e,l]===1,0,
MomentumPower[e,l]===2,e/.OnePointLoopRules2[l,m],
MomentumPower[e,l]===3,0,
True, e]

OnePointLoopReady[exp_,l_,m_]:=Module[{e},e=spExpand[exp];
Which[Head[e]===Plus,Map[OnePointLoopRulesSelecter[#,l,m]&,e],
Head[e]===Times \[Or] Head[e]===Power,OnePointLoopRulesSelecter[e,l,m],
Head[e]===Integer \[Or] Head[e]===Symbol, e LFA0[m^2],
(*e==0,0,*)
True, Print["--Head is ", Head[e]," .--"]
]]


(* Tadpole, i.e. one-point loop function.
ext: external particles; mom: momenta of the external particles;
int: intermediate particle *)
(*
Tadpole[lag_, ext_, mom_, in_] :=
 Module[{l, int, symfac, r}, int = Flatten[{in}];
  (*Symmetry factor*)symfac = If[AntiParticle[int] === int, 2, 1];
  If[(*If ext is a symbol,or an array*)Length[Flatten@{ext}] <= 1,
   r = TreeAmplitude[lag,
      Flatten@Join[{ext}, {int}, AntiParticle[{ext, int}]],
      Flatten@{mom, l, -mom, -l}]/symfac,
   (*If ext is a list of two lists,
   then the first (second) list means the initial (final) particles*)
   r = TreeAmplitude[lag,
      Flatten@Join[ext, {int}, AntiParticle[{int}]],
      Flatten@{mom, l, -l}]/symfac];
  OnePointLoopReady[r, l, M[Sequence @@ int]]]
*)

Tadpole[lag_, ext_, mom_, in_] :=
 Module[{l, int, symfac, r}, int = Flatten[{in}];
  (*Symmetry factor*)symfac = If[AntiParticle[int] === int, 2, 1];
  r=TreeAmplitude[lag,
      Flatten@Join[{ext}, {int}, AntiParticle[{ int}]],
      Flatten@{mom, l, -l}]/symfac;
  OnePointLoopReady[r, l, M[Sequence @@ int]]]

OnePoint=Tadpole;


(* ::Subsection:: *)
(*Two-point*)


(* Repalcing rules *)
(* convention: 1/(l^2-m1^2)*1/[(l+q)^2-m2^2] *)
TwoPointLoopRules1[l_,q_,m1_,m2_]:={(* Subscript[l, \[Mu]] *)
momentum[l,\[Mu]_]:>momentum[q,\[Mu]] LFB1[sp[q,q],m1^2,m2^2],
(* l\[CenterDot]p *)
sp[l,p_?(UnsameQ[l,#]&)]:>sp[p,q] LFB1[sp[q,q],m1^2,m2^2]}

TwoPointLoopRules2[l_,q_,m1_,m2_]:={(* l^2 *)
sp[l,l]:>LFA0[m2^2]+m1^2 LFB0[##],
(* Subscript[l, \[Mu]] Subscript[l, \[Nu]] *)
momentum[l,\[Mu]_] momentum[l,\[Nu]_]:>Metric[\[Mu],\[Nu]] LFB00[##]+momentum[q,\[Mu]] momentum[q,\[Nu]] LFB11[##],
(* Subscript[l, \[Mu]]l\[CenterDot]p *)
momentum[l,\[Mu]_] sp[l,p_?(UnsameQ[l,#]&)]:>momentum[p,\[Mu]] LFB00[##]+momentum[q,\[Mu]] sp[q,p] LFB11[##],
(* l\[CenterDot]Subscript[p, 1] l\[CenterDot]Subscript[p, 2 ] *)
sp[l,p1_?(UnsameQ[l,#]&)] sp[l,p2_?(UnsameQ[l,#]&)]:>sp[p1,p2] LFB00[##]+sp[q,p1] sp[q,p2] LFB11[##]}&[sp[q,q],m1^2,m2^2]

TwoPointLoopRules3[l_,q_,m1_,m2_]:={(* l^2 Subscript[l, \[Mu]] *)
sp[l,l]momentum[l,\[Mu]_]:>-momentum[q,\[Mu]] LFA0[m2^2]+m1^2 momentum[q,\[Mu]] LFB1[##],
(* l^2 l\[CenterDot]p *)
sp[l,l]sp[l,p_]:>-sp[q,p] LFA0[m2^2]+m1^2 sp[q,p] LFB1[##],
(* Subscript[l, \[Mu]] Subscript[l, \[Nu]] Subscript[l, \[Rho]] *)
momentum[l,\[Mu]_] momentum[l,\[Nu]_] momentum[l,\[Rho]_]:>Metric[\[Mu],\[Nu]] momentum[q,\[Rho]] LFB001[##]+
momentum[q,\[Mu]] momentum[q,\[Nu]] momentum[q,\[Rho]] LFB111[##],
(* l\[CenterDot]p Subscript[l, \[Nu]] Subscript[l, \[Rho]] *)
sp[l,p_?(UnsameQ[l,#]&)] momentum[l,\[Nu]_] momentum[l,\[Rho]_]:>momentum[p,\[Nu]] momentum[q,\[Rho]] LFB001[##]+
sp[q,p] momentum[q,\[Nu]] momentum[q,\[Rho]] LFB111[##],
(* l\[CenterDot]Subscript[p, 1] l\[CenterDot]Subscript[p, 2] Subscript[l, \[Rho]] *)
sp[l,p1_?(UnsameQ[l,#]&)] sp[l,p2_?(UnsameQ[l,#]&)] momentum[l,\[Rho]_]:>sp[p1,p2] momentum[q,\[Rho]] LFB001[##]+
sp[q,p1] sp[q,p2] momentum[q,\[Rho]] LFB111[##],
(* l\[CenterDot]Subscript[p, 1] l\[CenterDot]Subscript[p, 2] l\[CenterDot]Subscript[p, 3] *)
sp[l,p1_?(UnsameQ[l,#]&)] sp[l,p2_?(UnsameQ[l,#]&)] sp[l,p3_?(UnsameQ[l,#]&)]:>sp[p1,p2] sp[q,p3] LFB001[##]+
sp[q,p1] sp[q,p2] sp[q,p3] LFB111[##]}&[sp[q,q],m1^2,m2^2]

TwoPointLoopRules4[l_,q_,m1_,m2_]:={(* Subscript[l, \[Mu]] Subscript[l, \[Nu]] Subscript[l, \[Rho]] Subscript[l, \[Sigma]]  *)
momentum[l,\[Mu]_] momentum[l,\[Nu]_] momentum[l,\[Rho]_] momentum[l,\[Sigma]_]:>(Metric[\[Mu],\[Nu]] Metric[\[Rho],\[Sigma]]+
Metric[\[Mu],\[Rho]] Metric[\[Nu],\[Sigma]]+Metric[\[Mu],\[Sigma]] Metric[\[Nu],\[Rho]]) LFB0000[##]+
(Metric[\[Mu],\[Nu]] momentum[q,\[Rho]] momentum[q,\[Sigma]]+Metric[\[Mu],\[Rho]] momentum[q,\[Nu]] momentum[q,\[Sigma]]+
Metric[\[Mu],\[Sigma]] momentum[q,\[Rho]] momentum[q,\[Nu]]+Metric[\[Rho],\[Sigma]] momentum[q,\[Mu]] momentum[q,\[Nu]]+
Metric[\[Nu],\[Sigma]] momentum[q,\[Mu]] momentum[q,\[Rho]]+Metric[\[Rho],\[Nu]] momentum[q,\[Mu]] momentum[q,\[Sigma]]) LFB0011[##]+
momentum[q,\[Mu]] momentum[q,\[Nu]] momentum[q,\[Rho]] momentum[q,\[Sigma]] LFB1111[##],
(* Subscript[l, \[Mu]]l\[CenterDot]Subscript[p, 1]l\[CenterDot]Subscript[p, 2]l\[CenterDot]Subscript[p, 3] *)
momentum[l,\[Mu]_] sp[l,p1_?(UnsameQ[l,#]&)] sp[l,p2_?(UnsameQ[l,#]&)] sp[l,p3_?(UnsameQ[l,#]&)]:>
(momentum[p1,\[Mu]] sp[p2,p3]+momentum[p2,\[Mu]] sp[p1,p3]+momentum[p3,\[Mu]] sp[p1,p2]) LFB0000[##]+
(momentum[p1,\[Mu]] sp[p2,q]sp[p3,q]+momentum[p2,\[Mu]] sp[p1,q]sp[p3,q]+
momentum[p3,\[Mu]] sp[p2,q]sp[p1,q]+momentum[q,\[Mu]] sp[p1,q]sp[p2,p3]+
momentum[q,\[Mu]] sp[p2,q]sp[p1,p3]+momentum[q,\[Mu]] sp[p3,q]sp[p2,p1]) LFB0011[##]+
momentum[q,\[Mu]] sp[p1,q]sp[p2,q] sp[p3,q] LFB1111[##],
(* Subscript[l, \[Mu]] Subscript[l, \[Nu]] l^2  *)
sp[l,l]momentum[l,\[Mu]_] momentum[l,\[Nu]_]:>Metric[\[Mu],\[Nu]] (LFA00[m2^2]+m1^2 LFB00[##])+momentum[q,\[Mu]] momentum[q,\[Nu]](LFA0[m2^2]+m1^2 LFB11[##]),
(* Subscript[l, \[Mu]] l\[CenterDot]p l^2  *)
sp[l,l] sp[l,p_?(UnsameQ[l,#]&)] momentum[l,\[Mu]_]:>momentum[p,\[Mu]] (LFA00[m2^2]+m1^2 LFB00[##])+
momentum[q,\[Mu]] sp[p,q] (LFA0[m2^2]+m1^2 LFB11[##]),
(* l^2 l^2  *)
sp[l,l]^2:>Plus[##]LFA0[m2^2]+m1^4 LFB0[##]}&[sp[q,q],m1^2,m2^2]


(* selcting proper rules for two-point loops *)
TwoPointLoopRulesSelecter[e_,l_,q_,m1_,m2_]:=
Which[MomentumPower[e,l]===0,e LFB0[sp[q,q],m1^2,m2^2],
MomentumPower[e,l]===1,e/.TwoPointLoopRules1[l,q,m1,m2],
MomentumPower[e,l]===2,e/.TwoPointLoopRules2[l,q,m1,m2],
MomentumPower[e,l]===3,e/.TwoPointLoopRules3[l,q,m1,m2],
MomentumPower[e,l]===4,e/.TwoPointLoopRules4[l,q,m1,m2],
True, e]

TwoPointLoopReady[exp_,l_,q_,m1_,m2_]:=Module[{e},e=spExpand[exp];
Which[Head[e]===Plus,Map[TwoPointLoopRulesSelecter[#,l,q,m1,m2]&,e],
Head[e]===Times \[Or] Head[e]===Power,TwoPointLoopRulesSelecter[e,l,q,m1,m2],
e===0, 0,
True, Print["--Head is ",Head[e]," .--"]
]]


(* Two-point one-loop function *)
TwoPointRules=Rules->{};
Protect[Rules];
Options[TwoPoint]={TwoPointRules};

(* For instance, {{eta8,pim,pip},{pim,pip}}, the lengths of the two sublists are not equal, is not an array. In this case, use Length  *)
ArrayDepth2[a_]:=If[ArrayQ[a],ArrayDepth[a],Length[a]]

TwoPoint[lag_,ext_,mom_,int_,OptionsPattern[]]:=Module[{l,symfac,q,q34,r,args,tp,mand},
If[ArrayDepth2[ext]=!=ArrayDepth2[mom],Print["--TwoPoint:: External-particle and momentum lists do not match--"]];
(* Symmetry factor when the intermediate two particles are identical, need to be checked *)
symfac=If[int[[1]]===int[[2]],2,1];
If[ArrayDepth2[ext]==2,
(* total momentum *)
q=Plus@@mom[[1]];q34=Plus@@mom[[2]];
r=1/symfac I^(2-1)(*from vertices*) I^(2-1)(*from loop*) *
TreeAmplitude[lag,Flatten@Join[ext[[1]],AntiParticle[int]],Flatten@{mom[[1]],l,-l-q}]*
TreeAmplitude[lag,Flatten@Join[int,ext[[2]]],Flatten@{-l,l-q34,mom[[2]]}],
Print["--Wrong format of external-particle list--"]];
args=Sequence[sp[q,q],M[int[[1]]]^2,M[int[[2]]]^2];
(* express the amplitude in two-point loop functions *)
tp=TwoPointLoopReady[r,l,q,M[int[[1]]],M[int[[2]]]];
mand=Which[(* for 2->2 process, use MandelstamRules *)
Length[mom[[1]]]==2&&Length[mom[[2]]]==2,spExpand[tp]/.MandelstamRules,
(* for process with five external particles, use MandelstamRulesij *)
Length[Flatten[mom]]==5,
spExpand[tp]/.MandelstamRulesij,
(* Other cases *)
True,spExpand[tp]];
(* On-shell *)
mand/.OptionValue[Rules]//.Thread[Rule[Table[sp[#[[i]],#[[i]]],{i,Length[#]}]&[(Flatten@mom)],
Table[M[#[[i]]]^2,{i,Length[#]}]&[(Flatten@ext)]]]]


(* ::Subsection:: *)
(*Explicit loop functions*)


(* A0 loop, div = 1/(32 \[Pi]^2)(2/(d-4)-[ln(4\[Pi]) +\[CapitalGamma]'(1)+1] ) = \[Lambda] *)
LoopA0[msq_,div_,mu_]:=msq(2*div+1/(16 \[Pi]^2) Log[msq/mu^2])

(* B0 loop, i.e. J in Gass & Leutwyler's paper with a different sign *)
(* Overscript[J, _][s,m1^2,m2^2]=1/(32 \[Pi]^2) (2+(\[CapitalDelta]/s-\[CapitalSigma]/\[CapitalDelta]) Log[m2^2/m1^2]-(\[Lambda](s))/s Log[((s+\[Lambda](s))^2-dif^2)/((s-\[Lambda](s))^2-dif^2)]),
with \[CapitalDelta]=m1^2-m2^2, \[CapitalSigma]=m2^2-m1^2, \[Lambda](s)=(s-(m1+m2)^2)(s-(m1-m2)^2) *)
LoopJ[s_,m12_,m22_,div_,mu_]:=Module[{dif,sum,term},dif=m12-m22;sum=m12+m22;
term=If[m12===m22,(* rewrite for the case m1=m2 *)
Log[m12/mu^2]+1,1/dif (m12 Log[m12/mu^2]-m22 Log[m22/mu^2])];
2*div+term/(16 \[Pi]^2)-Jbar[s,m12,m22]]


(* tensor loop *)
LoopA00[msq_]:=msq/4 LFA0[msq]-msq^2/(128 \[Pi]^2)

LoopB1[s_,m12_,m22_]:=1/(2 s) (LFA0[m12]-LFA0[m22])+1/2 ((m22-m12)/s-1) LFB0[s,m12,m22]

LoopB00[s_,m12_,m22_]:=Module[{dif,sum,\[Nu]},dif=m12-m22;sum=m12+m22;\[Nu]=(s-m12+m22)^2-4 m22 s;
1/12 ((1+dif/s)LFA0[m12]+(1-dif/s)LFA0[m22]-\[Nu]/s LFB0[s,m12,m22]+(s-3 sum)/(24 \[Pi]^2))]
LoopB11[s_,m12_,m22_]:=Module[{dif,sum,\[Nu]},dif=m12-m22;sum=m12+m22;\[Nu]=(s-m12+m22)^2-4 m22 s;
1/(3 s) (-(1+dif/s)LFA0[m12]+(2+dif/s)LFA0[m22]+(\[Nu]/s+3 m12) LFB0[s,m12,m22]+(3 sum-s)/(96 \[Pi]^2))]

LoopB001[q2_,m12_,m22_]:=(LFA00[m12]-LFA00[m22])/(2 q2)+1/2 ((m22-m12)/q2-1)LFB00[q2,m12,m22]
LoopB111[q2_,m12_,m22_]:=(LFA00[m22]-LFA00[m12])/q2^2-LFA0[m22]/(2 q2)+((m22-m12)/q2-1)(1/2 LFB11[q2,m12,m22]-LFB00[q2,m12,m22]/q2)
(* Subscript[B, 0000] is only given for equal-mass case *)
LoopB0000[s_,m2_,m2_]:=1/120 ( (7 m2-s) LFA0[m2]+1/2 (s-4 m2)^2 LFB0[s,m2,m2]-1/(480 \[Pi]^2) (16 s^2-160 m2 s+465 m2^2) )


LoopFunction[exp_,div_,\[Mu]_]:=exp/.{LFB001->LoopB001,
LFB111->LoopB111,
LFB0000[s_,m2_,m2_]:>LoopB0000[s,m2,m2]}/.{
LFA00->LoopA00,LFB1->LoopB1,LFB00->LoopB00,LFB11->LoopB11}/.{
(* explicit expressions *)
LFA0[msq_]:>LoopA0[msq,div,\[Mu]],
(* Notice thee convention of Overscript[J, _] here is the same as the one in Gasser and Leutwyler,
and is different (sign and a factor of 16 \[Pi]^2) compared to Scherer hep-ph/0210398 *)
LFB0[qsq_,m1sq_,m2sq_]:>LoopJ[qsq,m1sq,m2sq,div,\[Mu]]
(* For loops with m1=m2, NOTICE different convention *)
(*
LFB0[qsq_,msq_,msq_]:>1/(16 \[Pi]^2) (div+Log[msq/\[Mu]^2]+1-Jbar[qsq]),
LFB00[qsq_,msq_,msq_]:>1/(96 \[Pi]^2) (3(msq-qsq/6)(div+Log[msq/\[Mu]^2])-1/6 qsq-2 (msq-qsq/4) Jbar[qsq]),
LFB11[qsq_,msq_,msq_]:>1/(48 \[Pi]^2) (div+Log[msq/\[Mu]^2]+5/6-(1-msq/qsq) Jbar[qsq])
*)
}

LF=LoopFunction;
