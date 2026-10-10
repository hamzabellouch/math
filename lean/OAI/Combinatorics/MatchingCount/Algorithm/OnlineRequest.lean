import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineStage
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineScheduleNat

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Transport ExecutableSource NumericLadder ExecutableScaling
open TreeTyped.Numbered Enlargement UnitRefresh ExecutableAdaptive
open ExecutableBottleneck ExecutableHierarchy ExecutableRefresh

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

def lengthAfter {A B : Type} [Codec A] [Codec B] {f : A→List B} (F : Realizer f) :
    Realizer (fun a=>(f a).length) := composition F listLength
lemma polynomial_lengthAfter {A B : Type} [Codec A] [Codec B] {f : A→List B} {F : Realizer f}
    (hF : PolynomialTime F) : PolynomialTime (lengthAfter F) :=
  polynomial_composition hF polynomial_listLength

def rangeAfter {A : Type} [Codec A] {f : A→ℕ} (F : Realizer f) :
    Realizer (fun a=>List.range (f a)) := composition F range

def listIndices {A : Type} [Codec A] : Realizer (fun xs : List A=>List.range xs.length) :=
  composition listLength range
lemma polynomial_listIndices {A : Type} [Codec A] : PolynomialTime (listIndices (A:=A)) :=
  polynomial_boundedRange polynomial_listLength Polynomial.X (fun xs=>by simpa using list_length_le_weight xs)

def indicesAfter {A B : Type} [Codec A] [Codec B] {f : A→List B} (F : Realizer f) :
    Realizer (fun a=>List.range (f a).length) := composition F listIndices
lemma polynomial_indicesAfter {A B : Type} [Codec A] [Codec B] {f : A→List B} {F : Realizer f}
    (hF : PolynomialTime F) : PolynomialTime (indicesAfter F) :=
  polynomial_composition hF polynomial_listIndices

abbrev PrecisionData := ScanInput×(ℕ×ℕ)

def scanError (x : PrecisionData) : ℕ :=
  2*(1+(x.1.1.2.2*(ladderQ x.1.1.1.1 x.1.1.1.2)^2+ladderQ x.1.1.1.1 x.1.1.1.2))+
  4*(8*x.2.1^2+4*x.2.1+3)+2*x.1.1.1.1^2*x.2.2

def scanErrorRealizer : Realizer scanError :=
  ((((constant 2).mulNat ((constant 1).addNat
    ((first.fst.snd.snd.mulNat (composition (composition first.fst.fst qRealizer) (fixedPower 2))).addNat
      (composition first.fst.fst qRealizer)))).addNat
    ((constant 4).mulNat ((((constant 8).mulNat (composition second.fst (fixedPower 2))).addNat
      ((constant 4).mulNat second.fst)).addNat (constant 3)))).addNat
    (((constant 2).mulNat (composition first.fst.fst.fst (fixedPower 2))).mulNat second.snd)).congr (fun _=>rfl)
lemma polynomial_scanError : PolynomialTime scanErrorRealizer := by
  unfold scanErrorRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_q
  have := polynomial_fixedPower 2
  simp only [Realizer.addNat,Realizer.mulNat]
  tree_cost

def precisionPlan (x : PrecisionData) : ((ℕ×ℕ)×ℕ)×ℕ :=
  (((Nat.clog 2 (discreteLadderSteps x.1.1.1.1 x.1.1.1.2 x.1.1.2.1 x.1.1.2.2 x.1.2 *scanError x*x.1.2),
      x.1.1.1.1),discreteLadderSteps x.1.1.1.1 x.1.1.1.2 x.1.1.2.1 x.1.1.2.2 x.1.2),
    Nat.clog 2 (6*x.2.1*x.1.2))
def precisionPlanRealizer : Realizer precisionPlan :=
  (pair (pair (pair
    (composition (((composition first scansRealizer).mulNat scanErrorRealizer).mulNat first.snd) clogTwo)
    first.fst.fst.fst) (composition first scansRealizer))
    (composition (((constant 6).mulNat second.fst).mulNat first.snd) clogTwo)).congr (fun _=>rfl)
lemma polynomial_precisionPlan : PolynomialTime precisionPlanRealizer := by
  unfold precisionPlanRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_scanError
  have := polynomial_scans
  have := polynomial_clogTwo
  simp only [Realizer.mulNat]
  tree_cost

abbrev RequestInput := SparseStageData×ℕ

def sourcePrecision (x : RequestInput) : PrecisionData :=
  let b:=sparseBagInput x.1
  (((((sourceVertices b).length,x.1.1.2.1.2),(x.1.1.2.1.1.2.length/2,x.1.1.2.2.1.length)),
    1000*(x.1.1.2.1.1.2.length/2)*x.2),
    ((sourceTables b).1.length,(sourceParents b).length))
def requestBagRealizer : Realizer (fun x : RequestInput=>sparseBagInput x.1) :=
  composition first sparseBagInputRealizer
def requestKRealizer : Realizer (fun x : RequestInput=>x.1.1.2.1.1.2.length/2) :=
  composition (pair (composition first.fst.snd.fst.fst.snd listLength) (constant 2)) quotient
def requestNDRealizer : Realizer (fun x : RequestInput=>((sourceVertices (sparseBagInput x.1)).length,x.1.1.2.1.2)) :=
  pair (composition (composition (g:=sourceVertices) requestBagRealizer sourceVerticesRealizer) listLength) first.fst.snd.fst.snd
def requestKTRealizer : Realizer (fun x : RequestInput=>(x.1.1.2.1.1.2.length/2,x.1.1.2.2.1.length)) :=
  pair requestKRealizer (composition first.fst.snd.snd.fst listLength)
def requestMRealizer : Realizer (fun x : RequestInput=>1000*(x.1.1.2.1.1.2.length/2)*x.2) :=
  ((constant 1000).mulNat requestKRealizer).mulNat second
def requestScanRealizer : Realizer (fun x : RequestInput=>
    ((((sourceVertices (sparseBagInput x.1)).length,x.1.1.2.1.2),
      (x.1.1.2.1.1.2.length/2,x.1.1.2.2.1.length)),1000*(x.1.1.2.1.1.2.length/2)*x.2)) :=
  pair (pair requestNDRealizer requestKTRealizer) requestMRealizer
def requestTablesRealizer : Realizer (fun x : RequestInput=>sourceTables (sparseBagInput x.1)) :=
  composition (f:=fun x : RequestInput=>sparseBagInput x.1) (g:=sourceTables)
    requestBagRealizer sourceTablesRealizer
def requestCatalogRealizer : Realizer (fun x : RequestInput=>(sourceTables (sparseBagInput x.1)).1) :=
  Realizer.fst (f:=fun x : RequestInput=>sourceTables (sparseBagInput x.1)) requestTablesRealizer
def requestEdgesRealizer : Realizer (fun x : RequestInput=>(sourceTables (sparseBagInput x.1)).1.length) :=
  lengthAfter (f:=fun x : RequestInput=>(sourceTables (sparseBagInput x.1)).1) requestCatalogRealizer
def requestLabelsRealizer : Realizer (fun x : RequestInput=>(sourceParents (sparseBagInput x.1)).length) :=
  composition (composition (g:=sourceParents) requestBagRealizer sourceParentsRealizer) listLength
def sourcePrecisionRealizer : Realizer sourcePrecision :=
  pair requestScanRealizer (pair requestEdgesRealizer requestLabelsRealizer)
lemma polynomial_requestBag : PolynomialTime requestBagRealizer :=
  polynomial_composition polynomial_first polynomial_sparseBagInput
lemma polynomial_requestK : PolynomialTime requestKRealizer := by
  unfold requestKRealizer
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_quotient
  tree_cost
lemma polynomial_requestND : PolynomialTime requestNDRealizer := by
  unfold requestNDRealizer
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_requestBag
  have := polynomial_sourceVertices
  tree_cost
lemma polynomial_requestKT : PolynomialTime requestKTRealizer := by
  unfold requestKTRealizer
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_requestK
  tree_cost
lemma polynomial_requestM : PolynomialTime requestMRealizer :=
  polynomial_mulNat (polynomial_mulNat (polynomial_constant _) polynomial_requestK) polynomial_second
lemma polynomial_requestScan : PolynomialTime requestScanRealizer :=
  TreeTyped.polynomial_pair (TreeTyped.polynomial_pair polynomial_requestND polynomial_requestKT) polynomial_requestM
lemma polynomial_requestTables : PolynomialTime requestTablesRealizer :=
  polynomial_composition polynomial_requestBag polynomial_sourceTables
lemma polynomial_requestCatalog : PolynomialTime requestCatalogRealizer :=
  polynomial_fst polynomial_requestTables
lemma polynomial_requestEdges : PolynomialTime requestEdgesRealizer :=
  polynomial_lengthAfter polynomial_requestCatalog
lemma polynomial_requestLabels : PolynomialTime requestLabelsRealizer :=
  polynomial_composition (polynomial_composition polynomial_requestBag
    polynomial_sourceParents) polynomial_listLength
lemma polynomial_sourcePrecision : PolynomialTime sourcePrecisionRealizer :=
  TreeTyped.polynomial_pair polynomial_requestScan (TreeTyped.polynomial_pair polynomial_requestEdges polynomial_requestLabels)

def sourceRequest (x : RequestInput) : OnlineSample.Request :=
  let plan:=precisionPlan (sourcePrecision x)
  (plan.1,(plan.2,List.range ((sourceTables (sparseBagInput x.1)).1.length)))
def requestPlanRealizer : Realizer (fun x : RequestInput=>precisionPlan (sourcePrecision x)) :=
  composition (g:=precisionPlan) sourcePrecisionRealizer precisionPlanRealizer
def requestIndicesRealizer : Realizer (fun x : RequestInput=>List.range (sourceTables (sparseBagInput x.1)).1.length) :=
  indicesAfter (f:=fun x : RequestInput=>(sourceTables (sparseBagInput x.1)).1) requestCatalogRealizer
def sourceRequestRealizer : Realizer sourceRequest :=
  pair requestPlanRealizer.fst (pair requestPlanRealizer.snd requestIndicesRealizer)
lemma polynomial_requestPlan : PolynomialTime requestPlanRealizer :=
  polynomial_composition polynomial_sourcePrecision polynomial_precisionPlan
lemma polynomial_requestIndices : PolynomialTime requestIndicesRealizer :=
  polynomial_indicesAfter polynomial_requestCatalog
lemma polynomial_sourceRequest : PolynomialTime sourceRequestRealizer :=
  TreeTyped.polynomial_pair (polynomial_fst polynomial_requestPlan)
    (TreeTyped.polynomial_pair (polynomial_snd polynomial_requestPlan) polynomial_requestIndices)

lemma sparseBagInput_source {G : GraphInput} {j : ℕ} (s : FiniteTrial.ScaleState G j)
    (K D : ℕ) (ft fq : List Bool) :
    sparseBagInput (OnlineStage.data s K D ft fq)=
      (((matrixRep s.activity,List.replicate (2*K+2) false),List.range G.n),List.replicate (2*K) false) := by
  have h:=sparseUpdateData_source s K D ft fq
  exact congrArg (fun x=>x.1.1.1.1) h

lemma sourcePrecision_source {G : GraphInput} [Nontrivial (Fin G.n)] (hn : 2≤G.n)
    {j : ℕ} (s : FiniteTrial.ScaleState G j) (K D S : ℕ) (ft fq : List Bool) :
    sourcePrecision (OnlineStage.data s K D ft fq,S)=
      (((((Fintype.card (SourceVertex (Fin G.n) K)),D),(K,ft.length)),1000*K*S),
        (Fintype.card (BagEdge (RationalSource.bags s.activity K)),Fintype.card (RationalSource.Label s.activity K))) := by
  unfold sourcePrecision
  rw [sparseBagInput_source]
  dsimp only [OnlineStage.data]
  rw [sourceVertices_length,sourceTables_catalog hn s.activity
    (fun i j=>(s.activity_pos i j).le) K,sourceParents_source hn s.activity
    (fun i j=>(s.activity_pos i j).le) K]
  simp only [List.length_replicate,Nat.mul_div_cancel_left _ (by decide : 0<2),sourceCatalog,List.length_ofFn,
    ExecutableDP.parentRep_length]

end MatchingFPRAS.OnlineSchedule

end OAI
