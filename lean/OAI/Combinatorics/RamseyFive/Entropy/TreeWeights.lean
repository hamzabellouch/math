import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.PrimitiveMessageWeights
import OAI.Combinatorics.RamseyFive.Geometry.OrientedPivotTree

namespace OAI

section
namespace SharpRamseyFive.MessageWeights
open scoped BigOperators
universe u v
lemma prod_weight_le (A : Type u) (B : Type v) [Fintype A] [Fintype B]
    (c : A→ℝ) (d : B→ℝ)
    (hc : (∑a,Real.exp (-c a))≤1) (hd : (∑b,Real.exp (-d b))≤1) :
    (∑m : A×B,Real.exp (-(c m.1+d m.2)))≤1 := by
  rw [Fintype.sum_prod_type]
  apply le_trans _ hc
  apply Finset.sum_le_sum
  intro a _
  simp only [neg_add,Real.exp_add,←Finset.mul_sum]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd (Real.exp_pos (-c a)).le
lemma option_bit_weight (A : Type u) [Fintype A] (c : A→ℝ)
    (hc : (∑a,Real.exp (-c a))≤1) :
    (∑m : Option A,Real.exp (-(Real.log 2+m.elim 0 c)))≤1 := by
  rw [Fintype.sum_option]
  simp only [Option.elim_none,Option.elim_some,add_zero,neg_add,Real.exp_add,
    ←Finset.mul_sum,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
  simp only [Real.exp_neg] at hc
  norm_num only [invOf_eq_inv, inv_mul_eq_div] at *
  linarith only [hc]
end SharpRamseyFive.MessageWeights
namespace SharpRamseyFive.TreeCodec
open BinaryTree MessageWeights
open scoped Classical BigOperators
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) (M : ∀a c,Ω a c→Type z)
  (left right : ∀a c t,M a c t→C)

noncomputable def slotCost (localCost : ∀a c t,M a c t→ℝ) :
    (b : BinaryTree A)→(ω : Tape Ω b)→(c : C)→Message Ω M left right b ω c→ℝ
  | .nil,_,_,_ => 0
  | .node _ _ _,_,_,none => Real.log 2
  | .node a l r,ω,c,some ⟨m,ml,mr⟩ => Real.log 2+localCost a c (ω.1 c) m+
      slotCost localCost l ω.2.1 (left a c (ω.1 c) m) ml+
      slotCost localCost r ω.2.2 (right a c (ω.1 c) m) mr

omit [Fintype C] in
lemma slotCost_weight [∀a c t,Fintype (M a c t)]
    (lc : ∀a c t,M a c t→ℝ)
    (hw : ∀a c t,(∑m : M a c t,Real.exp (-lc a c t m))≤1)
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) :
    (∑m : Message Ω M left right b ω c,Real.exp (-slotCost Ω M left right lc b ω c m))≤1 := by
  induction b generalizing c with
  | nil =>
    change (∑_m : PUnit, Real.exp (-(0:ℝ)))≤1
    simp
  | node a l r hl hr =>
    change (∑m : Option ((m : M a c (ω.1 c)) ×
      Message Ω M left right l ω.2.1 (left a c (ω.1 c) m) ×
      Message Ω M left right r ω.2.2 (right a c (ω.1 c) m)),
      Real.exp (-slotCost Ω M left right lc (.node a l r) ω c m))≤1
    have hh := sigma_weight_le (M a c (ω.1 c))
      (fun m=>Message Ω M left right l ω.2.1 (left a c (ω.1 c) m) ×
        Message Ω M left right r ω.2.2 (right a c (ω.1 c) m))
      (lc a c (ω.1 c))
      (fun m x=>slotCost Ω M left right lc l ω.2.1 (left a c (ω.1 c) m) x.1+
        slotCost Ω M left right lc r ω.2.2 (right a c (ω.1 c) m) x.2)
      (hw a c (ω.1 c)) (fun m=>prod_weight_le _ _ _ _ (hl ω.2.1 _) (hr ω.2.2 _))
    have hh' := option_bit_weight _ _ hh
    convert hh' using 1
    congr 1
    funext m
    cases m with
    | none => simp [slotCost]
    | some m => simp [slotCost,add_assoc]

omit [Fintype C] in
lemma slotCost_le (lc : ∀a c t,M a c t→ℝ)
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) (m : Message Ω M left right b ω c) :
    slotCost Ω M left right lc b ω c m≤cost Ω M left right lc b ω c m+
      (2*((retained Ω M left right b ω c m).numNodes:ℝ)+1)*Real.log 2 := by
  have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  induction b generalizing c with
  | nil => simp [slotCost,cost,retained,BinaryTree.numNodes,hlog]
  | node a l r hl hr =>
    cases m with
    | none => simp [slotCost,cost,retained,BinaryTree.numNodes]
    | some m =>
      have h1 := hl ω.2.1 _ m.2.1
      have h2 := hr ω.2.2 _ m.2.2
      simp only [slotCost,cost,retained,BinaryTree.numNodes,Nat.cast_add,Nat.cast_one]
      linarith only [h1,h2]
end SharpRamseyFive.TreeCodec
end

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry MessageWeights BinaryTree
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
omit [Finite K] [FiniteDimensional K V] in
lemma finiteNode_weight (p : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ) (hp : p.Normalized)
    (t : FiniteNodeTape p H q) :
    (∑m : FiniteNodeMessage p UB H q t,Real.exp (-finiteNodeCost p UB H q t m))≤1 := by
  exact sigma_weight_le _ _ _ _ (hp t.1) (fun m=>ambientPair_weight UB (p.decoded t.1 m) H q t.2)
variable [Fintype (ℙ K (Dual K (Dual K V)))]
omit [Finite K] in
lemma orientedNode_weight
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (UA : Finset (ℙ K V)) (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ)
    (hf : f.Normalized) (hr : r.Normalized) (t : OrientedNodeTape f r H q) :
    (∑m : OrientedNodeMessage f r UA UB H q t,Real.exp (-orientedNodeCost f r UA UB H q t m))≤1 := by
  convert sum_bit_weight _ _ _ _ (finiteNode_weight f UB H q hf t.1)
    (finiteNode_weight r (UA.map bidualPoint.toEmbedding) H q hr t.2) using 1
  congr 1
  funext m
  cases m <;> rfl
variable {ι : Type}
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
noncomputable def orientedPivotSlotCost (b : BinaryTree ι) (ω : OrientedPivotTreeTape f r b)
    (C : PivotContext K V) (m : OrientedPivotTreeMessage f r b ω C) : ℝ :=
  TreeCodec.slotCost (fun _ : ι=>OrientedPivotTape f r) (fun _ : ι=>OrientedPivotMessage f r)
    (fun _ : ι=>orientedPivotLeft f r) (fun _ : ι=>orientedPivotRight f r)
    (fun _ C t m=>orientedNodeCost (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t m)
    b ω C m
omit [Finite K] in
lemma orientedPivotTree_weight (hf : ∀C,(f C).Normalized) (hr : ∀C,(r C).Normalized)
    (b : BinaryTree ι) (ω : OrientedPivotTreeTape f r b) (C : PivotContext K V) :
    (∑m : OrientedPivotTreeMessage f r b ω C,Real.exp (-orientedPivotSlotCost f r b ω C m))≤1 := by
  let : ∀(_ : ι) C t,Fintype (OrientedPivotMessage f r C t) := fun _ _ _=>inferInstance
  exact TreeCodec.slotCost_weight _ _ _ _ _
    (fun _ C t=>orientedNode_weight (f C) (r C) C.1 C.2 _ _ (hf C) (hr C) t) b ω C

lemma fourPivotTree_weight (hd : finrank K V=5) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2 P τ R L₀
    let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
      (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding) P τ R L₀
    ∀(b : BinaryTree ι) (ω : OrientedPivotTreeTape f r b) (C : PivotContext K V),
      (∑m : OrientedPivotTreeMessage f r b ω C,Real.exp (-orientedPivotSlotCost f r b ω C m))≤1 := by
  dsimp only
  intro b ω C
  exact orientedPivotTree_weight _ _ (fun _=>fourFinite_weight _ _ _ _ _ _ _ _)
    (fun _=>fourFinite_weight _ _ _ _ _ _ _ _) b ω C
end SharpRamseyFive.ProjectiveIncidence

end OAI
