import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalDegree
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalFamilyEstimate
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalSelected

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateSupportRemoval
open MvPolynomial SymbolicHistory
open scoped BigOperators

theorem template_family_enlargement_error_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (B₀ V₀ : (j:ℕ) → Template.State k (j+1) → ℤ) (j : ℕ)
    (b : Bool) (s : ℤ) (e : Template.Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (D : Finset (Expr ι)) (hD : ∀ q ∈ D, q ∈ Template.obstructionExpressions k j b s e t) (i : ι)
    (S : Other i → Finset ℤ) (μ : Other i → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (α β H A : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hμ : ∀ u a, a ∈ S u → 0 ≤ μ u a) (hmass : ∀ u, ∑ a ∈ S u, μ u a=1)
    (hatom : ∀ u a, a ∈ S u → μ u a ≤ α)
    (hprime : ∀ p ∈ B, p.Prime) (hν : ∀ p ∈ B, 0 ≤ ν p) (hνmass : ∑ p ∈ B, ν p=1)
    (hνatom : ∀ p ∈ B, ν p ≤ β)
    (hsize : ∀ q ∈ D, ∀ x, (∀ u, x u ∈ S u) → eval x (eraseCoordinate i q.numerator) ≠ 0 →
      Real.log |((eval x (eraseCoordinate i q.numerator) : ℤ) : ℝ)| ≤ H)
    (r : (Other i → ℤ) → ℕ → Bool) (f : (Other i → ℤ) → ℕ → ℂ)
    (hf : ∀ x, (∀ u, x u ∈ S u) → ∀ p ∈ B, ‖f x p‖ ≤ A)
    (hgood : ∀ x, (∀ u, x u ∈ S u) → ∀ p ∈ B, r x p=true →
      ∀ u, HistoryReconstruction.Good (insertCoordinate i x (p:ℤ)) (e u))
    (hsupport : ∀ x, (∀ u, x u ∈ S u) → ∀ p ∈ B, r x p=true →
      Template.Supported k B₀ V₀ j s (Template.evalExpressions (insertCoordinate i x (p:ℤ)) e) t)
    (hfreq : ∀ q ∈ D, ∀ x, (∀ u, x u ∈ S u) → ∀ p ∈ B, r x p=true → q.DivisorsBelow p) :
    ‖independentPrimeMean S μ B ν (fun x p => familyCoprimeSupportedValue D (r x p) p
        (fun q => q.integerEval (insertCoordinate i x (p:ℤ))) (f x p))-
      independentPrimeMean S μ B ν (fun x p => familyPolynomialEnlargedValue D
        (fun q => eraseCoordinate i q.numerator) (r x p) (f x p))‖ ≤
      A * (∑ q ∈ D, ((q.degreeBudget : ℝ)*α+β*(H/Real.log 2))) := by
  classical
  have hg (q : Expr ι) (hq : q ∈ D) (x : Other i → ℤ) (hx : ∀ u, x u ∈ S u)
      (p : ℕ) (hp : p ∈ B) (hr : r x p=true) :
      HistoryReconstruction.Good (insertCoordinate i x (p:ℤ)) q :=
    Template.obstructionExpressions_good k B₀ V₀ j b s e t _
      (hgood x hx p hp hr) (hsupport x hx p hp hr) q (hD q hq)
  have hh := family_coprime_enlargement_error_le i D Expr.numerator Expr.denominator S μ B ν
    α β H A hα hβ hH hA hμ hmass hatom hprime hν hνmass hνatom hsize r
    (fun q x p => q.integerEval (insertCoordinate i x (p:ℤ))) f hf
    (fun q hq x hx p hp hr => q.integerEval_cleared _ (hg q hq x hx p hp hr).2)
    (fun q hq x hx p hp hr => q.denominator_isCoprime_of_divisorsBelow (hprime p hp)
      (hg q hq x hx p hp hr).1 (hfreq q hq x hx p hp hr))
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hA
  apply Finset.sum_le_sum
  intro q hq
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast erased_numerator_degree_le i q) hα

end Ostmann.Characters.TemplateSupportRemoval

end

end OAI
