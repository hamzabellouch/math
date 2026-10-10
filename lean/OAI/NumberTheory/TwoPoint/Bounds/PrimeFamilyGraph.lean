import OAI.NumberTheory.TwoPoint.Bounds.PrimeFamilyWeights
import OAI.NumberTheory.TwoPoint.Bounds.MaskedIntegerEdges
import OAI.NumberTheory.TwoPoint.Bounds.MatrixAction

namespace OAI

/-!
# The weighted-row lemma for concrete prime-family graph operators

This constructs the operators, rather than assuming a coordinate formula.
Arbitrary prime residue offsets cover both models. The symmetric gate can
include the progression test and any further edge deletions. The cutoff
uses the explicitly defined padding density.
-/

namespace TwoPointCorrelations

open Finset

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  {P : α → Type*} [∀ i, Fintype (P i)]

noncomputable def primeFamilyGraphOperator
    (value : (i : α) → P i → ℕ) (offset : (i : α) → P i → ℤ)
    (site : ι → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ι → ι → Prop) (x : (i : α) → P i) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  matrixOperator (maskedIntegerEdgeMatrix site Q u (eligible (familyTuple value x))
    g (familyCenter value offset x) L K (extra (familyTuple value x)) h
    (familyTuple value x) (gate (familyTuple value x)))

omit [DecidableEq α] [∀ i, Fintype (P i)] in
theorem primeFamilyGraphOperator_selfAdjoint
    (value : (i : α) → P i → ℕ) (offset : (i : α) → P i → ℤ)
    (site : ι → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ι → ι → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i)
    (x : (i : α) → P i) :
    IsSelfAdjoint (primeFamilyGraphOperator value offset site Q u eligible g L K extra h gate x) := by
  apply matrixOperator_selfAdjoint
  exact maskedIntegerEdgeMatrix_symmetric site Q u (eligible (familyTuple value x))
    g (familyCenter value offset x) L K (extra (familyTuple value x)) h
    (familyTuple value x) (gate (familyTuple value x)) (hgate _)

omit [DecidableEq α] [∀ i, Fintype (P i)] in
/-- The single-operator assertion of manuscript `q:weighted-rows`. -/
theorem primeFamilyGraphOperator_norm_le
    (value : (i : α) → P i → ℕ) (hprime : ∀ i p, (value i p).Prime)
    (offset : (i : α) → P i → ℤ) (site : ι → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ι → ι → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (x : (i : α) → P i) :
    ‖primeFamilyGraphOperator value offset site Q u eligible g L K extra h gate x‖ ≤ 2 * K := by
  let d := familyTuple value x
  let center := familyCenter value offset x
  let A := maskedIntegerEdgeMatrix site Q u (eligible d) g center L K (extra d) h d (gate d)
  have hperiod : ∀ q ∈ Q, ∀ n, center (n + (h * q * d : ℕ)) = center n :=
    fun q _ n => familyCenter_padding_periodic value offset x h q n
  change ‖matrixOperator A‖ ≤ _
  apply weighted_operator_norm_le (matrixOperator A) A (matrixOperator_apply A)
    (fun i => g (site i)) (fun i => |center (site i)|) (2 * K) (by positivity)
    (fun i => hg _) (fun i => abs_nonneg _) (fun i => familyCenter_abs_le_one value hprime offset x _)
  · intro i j
    dsimp [A]
    rw [maskedIntegerEdgeMatrix_symmetric site Q u (eligible d) g center L K (extra d) h d (gate d) (hgate d) i j, norm_star]
  · exact maskedIntegerEdgeMatrix_level site Q u (eligible d) g center L K (extra d) h d (gate d) hperiod
  · exact maskedIntegerEdgeMatrix_weighted_row site hinj Q u (eligible d) g center L K (extra d) h d (gate d) hL hK hu hg hperiod

/-- The square-function assertion of manuscript `q:weighted-rows`, with
its exact `4 K² (8W)^J` constant and the degree projection's support condition. -/
theorem primeFamilyGraphOperator_square_sum
    (value : (i : α) → P i → ℕ) (hprime : ∀ i p, (value i p).Prime)
    (offset : (i : α) → P i → ℤ) (site : ι → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ι → ι → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hV : ∀ i, ∑ p, (value i p : ℝ)⁻¹ ≤ 2 * W)
    (v : EuclideanSpace ℂ ι)
    (hdegree : ∀ k, v k ≠ 0 →
      (∑ i, ∑ p : P i, if (value i p : ℤ) ∣ offset i p + site k then (1 : ℝ) else 0) ≤
        6 * W * Fintype.card α) :
    (∑ x, ‖primeFamilyGraphOperator value offset site Q u eligible g L K extra h gate x v‖ ^ 2) ≤
      4 * K ^ 2 * (8 * W) ^ Fintype.card α * ‖v‖ ^ 2 := by
  let A (x : (i : α) → P i) := maskedIntegerEdgeMatrix site Q u (eligible (familyTuple value x))
    g (familyCenter value offset x) L K (extra (familyTuple value x)) h
    (familyTuple value x) (gate (familyTuple value x))
  have hlocal (x : (i : α) → P i) :
      (∑ i, ‖∑ j, A x i j * v j‖ ^ 2) ≤
        (2 * K) ^ 2 * ∑ i, |familyCenter value offset x (site i)| ^ 2 * ‖v i‖ ^ 2 := by
    have hh := maskedIntegerEdgeMatrix_localized_square site hinj Q u (eligible (familyTuple value x))
      g (familyCenter value offset x) L K (extra (familyTuple value x)) h (familyTuple value x)
      (gate (familyTuple value x)) (hgate _) hL hK hu hg
      (fun q _ n => familyCenter_padding_periodic value offset x h q n) (fun i => v i)
    convert hh using 1
    ring
  have hs := localized_square_sum A (fun x i => |familyCenter value offset x (site i)|)
    (2 * K) ((8 * W) ^ Fintype.card α) (fun i => v i) hlocal
    (fun i hi => familyCenter_square_sum_le value hprime offset (site i) W hV (hdegree i hi))
  calc
    _ = ∑ x, ∑ i, ‖∑ j, A x i j * v j‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, primeFamilyGraphOperator, matrixOperator_apply, A]
    _ ≤ (2 * K) ^ 2 * (8 * W) ^ Fintype.card α * ∑ i, ‖v i‖ ^ 2 := hs
    _ = _ := by rw [EuclideanSpace.norm_sq_eq]; ring

end TwoPointCorrelations

end OAI
