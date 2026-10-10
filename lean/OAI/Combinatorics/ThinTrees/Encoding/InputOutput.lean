import Mathlib
import OAI.Combinatorics.ThinTrees.Encoding.InputExpansion
import OAI.Combinatorics.ThinTrees.Sparsification.IterationRealization

namespace OAI

/-! Input output. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack GraphStack OrderedGraph Iteration.Stack
open MetricTests.RationalStep.Stack

def eEdges (R : ℕ) (x : E) : List (Fin x.val.m) :=
  List.ofFn (edgeEmbedding (Iteration.tree R (eProblem x).r (eProblem x).G))
def bEdges (R : ℕ) (x : B) : List x.val.Edge :=
  List.ofFn (fun i => x.val.originalCopy
    (edgeEmbedding (Iteration.tree R (bProblem x).r (bProblem x).G) i))
def eOutput (R : ℕ) (x : E) : Word := x.val.encodeEdges (eEdges R x)
def bOutput (R : ℕ) (x : B) : Word := x.val.encodeEdges (bEdges R x)

def eRun (R : ℕ) : Realizes eCode wordCode (eOutput R) :=
  ((ePrepare.then (treeProgram R)).then natToBinary.map).changeOutput wordCode (eOutput R) (by
    intro x
    simp only [treeData,List.map_ofFn,Function.comp_def,id_eq,eOutput,eEdges,
      ExplicitInput.encodeEdges,listCode,FramedMapRoutine.tape,wordCode,binaryNatCode]
    simp only [List.flatMap_def,List.map_ofFn,Function.comp_def,CurrentKS.DenseInputMachine.encodeNat_eq,KS.W01.encodeNat]
    erw [List.map_ofFn]
    rfl)

def lookupPair : Realizes (prodCode indicesCode natCode) fieldsCode
    (fun p => [p.1.getD p.2 0,0]) :=
  (((((second indicesCode natCode).both (first indicesCode natCode)).then (getD natCode 0)).then
    natToBinary).both (constant (prodCode indicesCode natCode) fieldsCode [0])).then
      (consList binaryNatCode)
instance poly_lookupPair : PolyTime lookupPair := by unfold lookupPair;infer_instance

def pairsOutput : Realizes (prodCode indicesCode indicesCode) fieldsCode
    (fun p => (p.2.map (fun i => [p.1.getD i 0,0])).flatten) :=
  lookupPair.mapCtx.then (joinList binaryNatCode)
instance poly_pairsOutput : PolyTime pairsOutput := by unfold pairsOutput;infer_instance

lemma bOutput_code (R : ℕ) (x : B) :
    fieldsCode (((treeData R (bProblem x)).map (fun i =>
      [(List.ofFn (fun e : Fin x.val.reduced.copies.length =>
        (x.val.reduced.copies.get e).1.val)).getD i 0,0])).flatten) = bOutput R x := by
  simp only [treeData,List.map_ofFn,Function.comp_def]
  rw [fieldsCode_flatten]
  simp only [List.map_ofFn,Function.comp_def,bOutput,bEdges,BinaryInput.encodeEdges,
    List.flatMap_def,List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext e
  have hget := getD_ofFn (fun i : Fin x.val.reduced.copies.length =>
    (x.val.reduced.copies.get i).1.val)
    (edgeEmbedding (Iteration.tree R (bProblem x).r (bProblem x).G) e) 0
  erw [hget]
  simp [fieldsCode,listCode,FramedMapRoutine.tape,BinaryInput.originalCopy,
    BinaryInput.liftCopy,binaryNatCode,CurrentKS.DenseInputMachine.encodeNat_eq,KS.W01.encodeNat]

def bRun (R : ℕ) : Realizes bCode wordCode (bOutput R) :=
  ((bRecords.both (bPrepare.then (treeProgram R))).then pairsOutput).changeOutput
    wordCode (bOutput R) (bOutput_code R)

lemma enum_toFinset {n : ℕ} (T : Finset (Fin n)) :
    (List.ofFn (edgeEmbedding T)).toFinset = T := by
  ext e
  simp only [List.mem_toFinset,List.mem_ofFn]
  constructor
  · rintro ⟨i,rfl⟩;exact embedding_mem T i
  · exact embedding_surj T
lemma enum_image {n : ℕ} {α : Type*} [DecidableEq α] (T : Finset (Fin n)) (f : Fin n → α) :
    (List.ofFn (fun i => f (edgeEmbedding T i))).toFinset = T.image f := by
  change (List.ofFn (f ∘ edgeEmbedding T)).toFinset = _
  rw [←List.map_ofFn]
  conv_rhs => rw [←enum_toFinset T]
  ext a
  simp

lemma thinTree_mono {n m k : ℕ} {G : MultiGraph n m} {T : Finset (Fin m)}
    {C D : ℝ} (hCD : C ≤ D) (h : ThinTree C k G T) : ThinTree D k G T := by
  refine ⟨h.1,fun S hS hS' => (h.2 S hS hS').trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact div_le_div_of_nonneg_right hCD (Nat.cast_nonneg _)

variable {R : ℕ} {C : ℝ}
variable (hC : 0 < C)
variable (hcorrect : ∀p : Problem,2 ≤ p.d+1 → 1 ≤ p.r → p.G.EdgeConnected p.r →
  ThinTree C p.r p.G (Iteration.tree R p.r p.G))

include hC hcorrect in
lemma eRun_good (x : E) : GoodOutput (2*C) (.explicit x.val) (eOutput R x) := by
  obtain ⟨hn,hk,hc⟩ := eProblem_good x
  have hT := makeProblem_thin x.val.graph _ x.val.k (hcorrect (eProblem x) hn hk hc)
  refine ⟨⟨eEdges R x,?_,rfl,?_⟩,?_⟩
  · exact List.nodup_ofFn.mpr (edgeEmbedding _).injective
  · dsimp only [eEdges]
    erw [enum_toFinset]
    exact thinTree_mono (by linarith : C≤2*C) hT
  · intro hh
    have hx := x.property.1
    change x.val.n=1 at hh
    omega

include hC hcorrect in
lemma bRun_good (x : B) : GoodOutput (2*C) (.binary x.val) (bOutput R x) := by
  classical
  obtain ⟨hn,hk,hc⟩ := bProblem_good x
  have hpos : 0<x.val.n := by have h:=x.property.1;omega
  have hT := makeProblem_thin x.val.reduced.expanded hpos (x.val.n^2)
    (hcorrect (bProblem x) hn hk hc)
  have hinj := x.val.originalCopy_injOn hpos hT.1
  have hthin := x.val.expanded_lift_thinTree hpos x.property.2.1 hC.le hT
  refine ⟨⟨bEdges R x,?_,rfl,?_⟩,?_⟩
  · apply List.nodup_ofFn.mpr
    intro i j he
    apply (edgeEmbedding _).injective
    exact hinj (embedding_mem _ i) (embedding_mem _ j) he
  · convert hthin using 1
    simp only [BinaryInput.selected,bEdges,Finset.map_eq_image]
    erw [enum_image]
    erw [Finset.image_image]
    rfl
  · intro hh
    have hx := x.property.1
    change x.val.n=1 at hh
    omega

variable (htime : ∀{ι : Type} {L : ι → ℕ} (a : ι → Problem),
  IsPoly L (fun i => (problemCode (a i)).length) →
  (∀i,2 ≤ (a i).d+1 ∧ 1 ≤ (a i).r ∧ (a i).G.EdgeConnected (a i).r) →
  RunsPoly L (treeProgram R) a)

include htime in
lemma runsPoly_eRun {ι : Type} {L : ι → ℕ} (a : ι → E)
    (ha : IsPoly L (fun i => (eCode (a i)).length)) : RunsPoly L (eRun R) a := by
  unfold eRun
  apply RunsPoly.changeOutput
  apply RunsPoly.then_poly
  have hp := RunsPoly.of_poly ePrepare a ha
  exact hp.then (htime _ hp.output (fun i => eProblem_good (a i)))
include htime in
lemma runsPoly_bRun {ι : Type} {L : ι → ℕ} (a : ι → B)
    (ha : IsPoly L (fun i => (bCode (a i)).length)) : RunsPoly L (bRun R) a := by
  unfold bRun
  apply RunsPoly.changeOutput
  apply RunsPoly.then_poly
  refine (RunsPoly.of_poly bRecords a ha).both ?_
  have hp := RunsPoly.of_poly bPrepare a ha
  exact hp.then (htime _ hp.output (fun i => bProblem_good (a i)))

end AlgorithmicThinTrees.InputStack
end

end OAI
