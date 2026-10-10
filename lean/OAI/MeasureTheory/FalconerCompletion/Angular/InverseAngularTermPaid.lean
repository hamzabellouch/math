import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.AngularDerivativeStar
import OAI.MeasureTheory.FalconerCompletion.Angular.InverseAngularTerms

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
variable {n : ℕ} {α : Type*} [DecidableEq α]

lemma inverseAngularTermND_paid (j : ℕ) (S : Finset α) (D : α → ℝ) {M r : ℝ}
    (hM : 1 ≤ M) (hr : 0 ≤ r) (hpaid : r*M^2 ≤ 1)
    (hD₀ : ∀ i ∈ S, 0 ≤ D i) (hD : ∀ i ∈ S, D i ≤ M)
    {a : ℂ × (α → List (SphereAmbientND n →L[ℝ] SphereAmbientND n))}
    (ha : a ∈ inverseAngularTermsND j S) :
    ‖(r:ℂ)^j * (a.1*((∏ i ∈ S, D i^(a.2 i).length:ℝ):ℂ))‖ ≤ ‖a.1‖ := by
  have hp : 0 ≤ ∏ i ∈ S, D i^(a.2 i).length :=
    Finset.prod_nonneg (fun i hi => pow_nonneg (hD₀ i hi) _)
  rw [norm_mul,norm_pow,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
  calc
    r^j * (‖a.1‖*(∏ i ∈ S,D i^(a.2 i).length)) =
        ‖a.1‖*(r^j*(∏ i ∈ S,D i^(a.2 i).length)) := by ring
    _ ≤ ‖a.1‖*1 := mul_le_mul_of_nonneg_left
      (assignedAngularScaleND_paid S D a.2 hM hr hpaid hD₀ hD
        (inverseAngularTermsND_budget j S ha)) (norm_nonneg _)
    _ = _ := mul_one _

lemma inverseAngularTermsND_paid_cost (j : ℕ) (S : Finset α) (D : α → ℝ) {M r : ℝ}
    (hM : 1 ≤ M) (hr : 0 ≤ r) (hpaid : r*M^2 ≤ 1)
    (hD₀ : ∀ i ∈ S, 0 ≤ D i) (hD : ∀ i ∈ S, D i ≤ M) :
    (((inverseAngularTermsND (n := n) j S).map (fun a =>
      ‖(r:ℂ)^j * (a.1*((∏ i ∈ S, D i^(a.2 i).length:ℝ):ℂ))‖)).sum) ≤
      inverseAngularCostND n j*(max 1 (S.card:ℝ))^(2*j) := by
  apply le_trans _ (inverseAngularTermsND_cost j S)
  apply List.sum_le_sum
  intro a ha
  exact inverseAngularTermND_paid j S D hM hr hpaid hD₀ hD ha

lemma inverseAngularTermsND_retention (j : ℕ) (S : Finset α)
    (f : α → SmoothFunctionND (SphereAmbientND n)) (D : α → ℝ)
    (hf : ∀ i ∈ S, Function.Even (f i).1)
    {a : ℂ × (α → List (SphereAmbientND n →L[ℝ] SphereAmbientND n))}
    (ha : a ∈ inverseAngularTermsND j S) :
    (∑ i ∈ S, (a.2 i).length ≤ 2*j) ∧
    ∀ i ∈ S, Function.Even (normalizedAngularWordND (D i) (a.2 i) (f i)).1 ∧
      tsupport (normalizedAngularWordND (D i) (a.2 i) (f i)).1 ⊆ tsupport (f i).1 := by
  refine ⟨inverseAngularTermsND_budget j S ha,?_⟩
  intro i hi
  exact ⟨normalizedAngularWordND_even _ _ _ (hf i hi),normalizedAngularWordND_support _ _ _⟩

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
