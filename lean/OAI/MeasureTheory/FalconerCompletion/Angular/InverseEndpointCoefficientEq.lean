import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.InverseAngularTermPaid
import OAI.MeasureTheory.FalconerCompletion.Angular.InverseEndpointCoefficient

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set
variable {n : ℕ} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
local notation "Assignment" => ℂ × ((ι ⊕ κ) → List (SphereAmbientND n →L[ℝ] SphereAmbientND n))

omit [DecidableEq ι] [DecidableEq κ] in
lemma inverseEndpointCoefficientND_eq (S : Finset ι) (T : Finset κ)
    (D : ι → ℝ) (E : κ → ℝ) (a : Assignment) :
    inverseEndpointCoefficientND S T D E a =
      a.1*((∏ i ∈ S.disjSum T, Sum.elim D E i^(a.2 i).length:ℝ):ℂ) := by
  simp only [inverseEndpointCoefficientND,Finset.prod_disjSum,Sum.elim_inl,Sum.elim_inr]

lemma inverseEndpointCoefficientND_paid_cost (j : ℕ) (S : Finset ι) (T : Finset κ)
    (D : ι → ℝ) (E : κ → ℝ) {M t : ℝ}
    (hM : 1 ≤ M) (ht : 0 ≤ t) (hpaid : t*M^2 ≤ 1)
    (hD₀ : ∀ i ∈ S, 0 ≤ D i) (hE₀ : ∀ k ∈ T, 0 ≤ E k)
    (hD : ∀ i ∈ S, D i ≤ M) (hE : ∀ k ∈ T, E k ≤ M) :
    (((inverseAngularTermsND (n := n) j (S.disjSum T)).map (fun a =>
      ‖(t:ℂ)^j*inverseEndpointCoefficientND S T D E a‖)).sum) ≤
    inverseAngularCostND n j*(max 1 ((S.card+T.card:ℕ):ℝ))^(2*j) := by
  have hz : ∀ i ∈ S.disjSum T, 0 ≤ Sum.elim D E i := by
    intro i hi
    cases i with
    | inl i => exact hD₀ i (Finset.inl_mem_disjSum.mp hi)
    | inr k => exact hE₀ k (Finset.inr_mem_disjSum.mp hi)
  have hu : ∀ i ∈ S.disjSum T, Sum.elim D E i ≤ M := by
    intro i hi
    cases i with
    | inl i => exact hD i (Finset.inl_mem_disjSum.mp hi)
    | inr k => exact hE k (Finset.inr_mem_disjSum.mp hi)
  simpa only [inverseEndpointCoefficientND_eq,Finset.card_disjSum] using
    inverseAngularTermsND_paid_cost (n := n) j (S.disjSum T) (Sum.elim D E) hM ht hpaid hz hu

noncomputable def paidSpatialCoefficientND (j : ℕ) (S : Finset ι) (T : Finset κ)
    (D : ι → ℝ) (E : κ → ℝ) (t δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K)
    (a : Assignment) (ξ : EuclideanSpace ℝ (Fin (n+1))) : ℂ :=
  ((t:ℂ)^j*inverseEndpointCoefficientND S T D E a)*
    SpatialFourierND.spatialFourierCoeff (n+1) δ K hδ hK j ξ

omit [DecidableEq ι] [DecidableEq κ] in
lemma paidSpatialCoefficientND_measurable (j : ℕ) (S : Finset ι) (T : Finset κ)
    (D : ι → ℝ) (E : κ → ℝ) (t δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K)
    (a : Assignment) : Measurable (paidSpatialCoefficientND j S T D E t δ K hδ hK a) :=
  (SpatialFourierND.spatialFourierCoeff (n+1) δ K hδ hK j).continuous.measurable.const_mul _

omit [DecidableEq ι] [DecidableEq κ] in
lemma paidSpatialCoefficientND_integrable (j : ℕ) (S : Finset ι) (T : Finset κ)
    (D : ι → ℝ) (E : κ → ℝ) (t δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K)
    (a : Assignment) : Integrable (paidSpatialCoefficientND j S T D E t δ K hδ hK a) :=
  (SpatialFourierND.spatialFourierCoeff (n+1) δ K hδ hK j).integrable.const_mul _

omit [DecidableEq ι] [DecidableEq κ] in
lemma paidSpatialCoefficientND_norm_integral (j : ℕ) (S : Finset ι) (T : Finset κ)
    (D : ι → ℝ) (E : κ → ℝ) (t δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K)
    (a : Assignment) :
    (∫ ξ, ‖paidSpatialCoefficientND j S T D E t δ K hδ hK a ξ‖) =
      ‖(t:ℂ)^j*inverseEndpointCoefficientND S T D E a‖*
        SpatialFourierND.spatialFourierCost (n+1) δ K hδ hK j := by
  simp only [paidSpatialCoefficientND,norm_mul,integral_const_mul,SpatialFourierND.spatialFourierCost]

lemma paidSpatialCoefficientND_cost (j : ℕ) (S : Finset ι) (T : Finset κ)
    (D : ι → ℝ) (E : κ → ℝ) {M t : ℝ}
    (hM : 1 ≤ M) (ht : 0 ≤ t) (hpaid : t*M^2 ≤ 1)
    (hD₀ : ∀ i ∈ S, 0 ≤ D i) (hE₀ : ∀ k ∈ T, 0 ≤ E k)
    (hD : ∀ i ∈ S, D i ≤ M) (hE : ∀ k ∈ T, E k ≤ M)
    (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K) :
    (((inverseAngularTermsND (n := n) j (S.disjSum T)).map (fun a =>
      ((2:ℝ)^((n:ℝ)/2)*(2:ℝ)^j)*
        ∫ ξ, ‖paidSpatialCoefficientND j S T D E t δ K hδ hK a ξ‖)).sum) ≤
    (((2:ℝ)^((n:ℝ)/2)*(2:ℝ)^j)*SpatialFourierND.spatialFourierCost (n+1) δ K hδ hK j*
      inverseAngularCostND n j)*(max 1 ((S.card+T.card:ℕ):ℝ))^(2*j) := by
  simp_rw [paidSpatialCoefficientND_norm_integral]
  have hc : 0 ≤ ((2:ℝ)^((n:ℝ)/2)*(2:ℝ)^j)*
      SpatialFourierND.spatialFourierCost (n+1) δ K hδ hK j :=
    mul_nonneg (by positivity) (SpatialFourierND.spatialFourierCost_nonneg _ _ _ _ _ _)
  have hh := mul_le_mul_of_nonneg_left
    (inverseEndpointCoefficientND_paid_cost (n := n) j S T D E hM ht hpaid hD₀ hE₀ hD hE) hc
  calc
    _ = (((2:ℝ)^((n:ℝ)/2)*(2:ℝ)^j)*SpatialFourierND.spatialFourierCost (n+1) δ K hδ hK j)*
      (((inverseAngularTermsND (n := n) j (S.disjSum T)).map (fun a =>
        ‖(t:ℂ)^j*inverseEndpointCoefficientND S T D E a‖)).sum) := by
        rw [← List.sum_map_mul_left]
        apply congrArg List.sum
        apply List.map_congr_left
        intro a ha
        ring
    _ ≤ _ := by simpa only [mul_assoc] using hh

noncomputable def fullInverseCoefficientCostND (n J : ℕ) (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K) : ℝ :=
  ∑ j ∈ Finset.range (J+1),
    ((2:ℝ)^((n:ℝ)/2)*(2:ℝ)^j)*SpatialFourierND.spatialFourierCost (n+1) δ K hδ hK j*
      inverseAngularCostND n j

lemma fullInverseCoefficientCostND_nonneg (n J : ℕ) (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K) :
    0 ≤ fullInverseCoefficientCostND n J δ K hδ hK := by
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (by positivity)
    (SpatialFourierND.spatialFourierCost_nonneg _ _ _ _ _ _)) (inverseAngularCostND_nonneg _ _)

lemma full_paidSpatialCoefficientND_cost (J : ℕ) (S : Finset ι) (T : Finset κ)
    (D : ι → ℝ) (E : κ → ℝ) {M t : ℝ}
    (hM : 1 ≤ M) (ht : 0 ≤ t) (hpaid : t*M^2 ≤ 1)
    (hD₀ : ∀ i ∈ S, 0 ≤ D i) (hE₀ : ∀ k ∈ T, 0 ≤ E k)
    (hD : ∀ i ∈ S, D i ≤ M) (hE : ∀ k ∈ T, E k ≤ M)
    (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K) :
    (∑ j ∈ Finset.range (J+1),
      ((inverseAngularTermsND (n := n) j (S.disjSum T)).map (fun a =>
        ((2:ℝ)^((n:ℝ)/2)*(2:ℝ)^j)*
          ∫ ξ, ‖paidSpatialCoefficientND j S T D E t δ K hδ hK a ξ‖)).sum) ≤
      fullInverseCoefficientCostND n J δ K hδ hK*
        (max 1 ((S.card+T.card:ℕ):ℝ))^(2*J) := by
  rw [fullInverseCoefficientCostND,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  apply (paidSpatialCoefficientND_cost j S T D E hM ht hpaid hD₀ hE₀ hD hE δ K hδ hK).trans
  apply mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (le_max_left _ _) (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ (Finset.mem_range.mp hj))))
  exact mul_nonneg (mul_nonneg (by positivity)
    (SpatialFourierND.spatialFourierCost_nonneg _ _ _ _ _ _)) (inverseAngularCostND_nonneg _ _)

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
