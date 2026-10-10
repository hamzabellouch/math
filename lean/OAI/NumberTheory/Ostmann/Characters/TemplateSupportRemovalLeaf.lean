import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalDegree
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalEstimate

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateSupportRemoval
open MvPolynomial SymbolicHistory
open scoped BigOperators

theorem template_leaf_enlargement_error_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (B₀ V₀ : (j:ℕ) → Template.State k (j+1) → ℤ) (j : ℕ)
    (s : ℤ) (e : Template.Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (b : Bool) (q : Template.BottomExpression (ι:=ι) k)
    (hq : q ∈ Template.bottomExpressions k j b s e t) (i : ι)
    (S : Other i → Finset ℤ) (μ : Other i → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (α β H A : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hμ : ∀ u a, a ∈ S u → 0 ≤ μ u a) (hmass : ∀ u, ∑ a ∈ S u, μ u a=1)
    (hatom : ∀ u a, a ∈ S u → μ u a ≤ α)
    (hprime : ∀ p ∈ B, p.Prime) (hν : ∀ p ∈ B, 0 ≤ ν p) (hνmass : ∑ p ∈ B, ν p=1)
    (hνatom : ∀ p ∈ B, ν p ≤ β)
    (hsize : ∀ x, (∀ u, x u ∈ S u) → eval x (eraseCoordinate i (Template.periodExpression k q.2.2).numerator) ≠ 0 →
      Real.log |((eval x (eraseCoordinate i (Template.periodExpression k q.2.2).numerator) : ℤ) : ℝ)| ≤ H)
    (r : (Other i → ℤ) → ℕ → Bool) (f : (Other i → ℤ) → ℕ → ℂ)
    (hf : ∀ x, (∀ u, x u ∈ S u) → ∀ p ∈ B, ‖f x p‖ ≤ A)
    (hgood : ∀ x, (∀ u, x u ∈ S u) → ∀ p ∈ B, r x p=true →
      ∀ u, HistoryReconstruction.Good (insertCoordinate i x (p:ℤ)) (e u))
    (hsupport : ∀ x, (∀ u, x u ∈ S u) → ∀ p ∈ B, r x p=true →
      Template.Supported k B₀ V₀ j s (Template.evalExpressions (insertCoordinate i x (p:ℤ)) e) t)
    (hden : ∀ x, (∀ u, x u ∈ S u) → ∀ p ∈ B, r x p=true → IsCoprime (p:ℤ) (Template.periodExpression k q.2.2).denominator) :
    ‖independentPrimeMean S μ B ν (fun x p => coprimeSupportedValue (r x p) p
        (Template.period k 0 (Template.evalExpressions (insertCoordinate i x (p:ℤ)) q.2.2)) (f x p))-
      independentPrimeMean S μ B ν (fun x p =>
        polynomialEnlargedValue (eraseCoordinate i (Template.periodExpression k q.2.2).numerator) (r x p) (f x p))‖ ≤
      A*(((Template.periodExpression k q.2.2).degreeBudget:ℝ)*α+β*(H/Real.log 2)) := by
  have hh := cleared_coprime_enlargement_error_le i (Template.periodExpression k q.2.2).numerator (Template.periodExpression k q.2.2).denominator S μ B ν
    α β H A hα hβ hH hA hμ hmass hatom hprime hν hνmass hνatom hsize r
    (fun x p => Template.period k 0 (Template.evalExpressions (insertCoordinate i x (p:ℤ)) q.2.2)) f hf
    (fun x hx p hp hr => (Template.bottom_period_cleared k B₀ V₀ j b s e t _
      (hgood x hx p hp hr) (hsupport x hx p hp hr) q hq).2) hden
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hA
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast erased_numerator_degree_le i (Template.periodExpression k q.2.2)) hα

end Ostmann.Characters.TemplateSupportRemoval

end

end OAI
