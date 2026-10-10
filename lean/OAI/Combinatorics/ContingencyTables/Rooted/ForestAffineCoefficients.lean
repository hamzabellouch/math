import OAI.Combinatorics.ContingencyTables.Counting.CompanionFactorialApplication
import OAI.Combinatorics.ContingencyTables.Transport.AffinePenalty

namespace OAI

/-! # The actual maximum-forest cut coefficients of tree completions -/

namespace ContingencyTables.ForestAffineCoefficients

open scoped BigOperators Classical
open CompanionFactorialApplication GraphIntegralCompletion GraphCompletionCounts
open ForestCapacity ForestCut MaximumForest

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def edge (t : I×J) : Sym2 (I⊕J) := s(Sum.inl t.1,Sum.inr t.2)

noncomputable def cutVertex (A : Instance I J) (t : TreeCell A.T) : I⊕J :=
  Classical.choose (exists_root_avoiding_side A.T A.hT t.property
    (componentRoot A.T (.inl t.val.1)) (componentRoot_reachable A.T (.inl t.val.1)).symm)

noncomputable def cutSide (A : Instance I J) (t : TreeCell A.T) (v : I⊕J) : Bool :=
  side (A.T.deleteEdges {edge t.val}) (cutVertex A t) v

lemma cut_properties (A : Instance I J) (t : TreeCell A.T) :
    A.T.Reachable (componentRoot A.T (.inl t.val.1)) (cutVertex A t) ∧
      cutSide A t (componentRoot A.T (.inl t.val.1))=false ∧
      cutSide A t (.inl t.val.1)≠cutSide A t (.inr t.val.2) :=
  Classical.choose_spec (exists_root_avoiding_side A.T A.hT t.property
    (componentRoot A.T (.inl t.val.1)) (componentRoot_reachable A.T (.inl t.val.1)).symm)

noncomputable def sign (A : Instance I J) (t : TreeCell A.T) (a : I×J) : ℝ :=
  indicator (cutSide A t (.inl a.1))-indicator (cutSide A t (.inr a.2))

lemma sign_abs_le_one (A : Instance I J) (t : TreeCell A.T) (a : I×J) :
    |sign A t a| ≤ 1 := by
  unfold sign
  cases cutSide A t (.inl a.1) <;> cases cutSide A t (.inr a.2) <;> norm_num [indicator]

lemma sign_abs_self (A : Instance I J) (t : TreeCell A.T) : |sign A t t.val|=1 :=
  abs_indicator_sub (cut_properties A t).2.2

lemma sign_self_ne_zero (A : Instance I J) (t : TreeCell A.T) : sign A t t.val≠0 := by
  intro hz
  have hh := sign_abs_self A t
  rw [hz,abs_zero] at hh
  norm_num at hh

noncomputable def coefficient (A : Instance I J) (t : TreeCell A.T) (a : I×J) : ℝ :=
  if A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)
  then -sign A t a/sign A t t.val else 0

lemma coefficient_abs_le_one (A : Instance I J) (t : TreeCell A.T) (a : I×J) :
    |coefficient A t a| ≤ 1 := by
  unfold coefficient
  split_ifs
  · rw [abs_div,abs_neg,sign_abs_self,div_one]
    exact sign_abs_le_one A t a
  · norm_num

/-- A nonzero tree coefficient crosses the actual edge-deletion cut,
so maximum total capacity bounds the contributing free capacity. -/
lemma capacity_le_of_coefficient_ne_zero (A : Instance I J) (t : TreeCell A.T) (a : I×J)
    (ha : coefficient A t a≠0) : A.b a.1 a.2 ≤ A.b t.val.1 t.val.2 := by
  have hfree : A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2) := by
    by_contra hh
    exact ha (by simp only [coefficient,hh,ite_false])
  have hcross : cutSide A t (.inl a.1)≠cutSide A t (.inr a.2) := by
    intro he
    apply ha
    simp [coefficient, hfree, sign, he]
  have hh := crossing_free_edge_le (cellGraph A.small) A.T (capacity A.b)
    A.hTG A.hT A.hmax (edge t.val) (by simpa [edge] using t.property)
    (cutVertex A t) (show (cellGraph A.small).Adj (.inl a.1) (.inr a.2) from hfree.1)
    hfree.2 hcross
  simpa only [edge,capacity_cell] using hh

/-- Scaling a free coordinate by (b_free+1)/B and normalizing a tree
value by b_tree gives coefficients at most 2/B, including structural
zero coefficients. This is the precise forest input to the evaluator's
Lipschitz estimate. -/
theorem normalized_coefficient_bound (A : Instance I J) (t : TreeCell A.T) (a : I×J)
    (B : ℝ) (hB : 0 < B) :
    |coefficient A t a*((A.b a.1 a.2:ℝ)+1)/B/(A.b t.val.1 t.val.2:ℝ)| ≤ 2/B := by
  have hbNat := (A.hlarge _ _ (A.hTG t.property)).2
  have hb : (1:ℝ) ≤ A.b t.val.1 t.val.2 := by exact_mod_cast hbNat
  by_cases ha : coefficient A t a=0
  · simp only [ha,zero_mul,zero_div,abs_zero]
    positivity
  have hcap : (A.b a.1 a.2:ℝ) ≤ A.b t.val.1 t.val.2 := by
    exact_mod_cast capacity_le_of_coefficient_ne_zero A t a ha
  rw [abs_div,abs_div,abs_mul,abs_of_pos hB,abs_of_pos (by linarith : (0:ℝ)<A.b t.val.1 t.val.2),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (A.b a.1 a.2:ℝ)+1)]
  apply (div_le_iff₀ (by linarith : (0:ℝ)<A.b t.val.1 t.val.2)).mpr
  rw [div_le_iff₀ hB]
  have hcoef := coefficient_abs_le_one A t a
  have hh := mul_le_mul_of_nonneg_right hcoef (by positivity : (0:ℝ) ≤ (A.b a.1 a.2:ℝ)+1)
  field_simp [hB.ne']
  nlinarith

end ContingencyTables.ForestAffineCoefficients

end OAI
