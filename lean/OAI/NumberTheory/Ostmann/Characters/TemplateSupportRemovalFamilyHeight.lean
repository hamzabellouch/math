import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalFamily
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalHeightLog

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateSupportRemoval
open MvPolynomial SymbolicHistory
open scoped BigOperators

theorem template_family_height_enlargement_error_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (B₀ V₀ : (j:ℕ) → Template.State k (j+1) → ℤ) (j : ℕ)
    (b : Bool) (s : ℤ) (e : Template.Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (D : Finset (Expr ι)) (hD : ∀ q ∈ D, q ∈ Template.obstructionExpressions k j b s e t) (i : ι)
    (S : Other i → Finset ℤ) (μ : Other i → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (α β H A : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : Real.log 2 ≤ H) (hA : 0 ≤ A)
    (hμ : ∀ u a, a ∈ S u → 0 ≤ μ u a) (hmass : ∀ u, ∑ a ∈ S u, μ u a=1)
    (hatom : ∀ u a, a ∈ S u → μ u a ≤ α)
    (hprime : ∀ p ∈ B, p.Prime) (hν : ∀ p ∈ B, 0 ≤ ν p) (hνmass : ∑ p ∈ B, ν p=1)
    (hνatom : ∀ p ∈ B, ν p ≤ β)
    (Z : ℕ) (hsyntax : ∀ q ∈ D, q.syntaxSize ≤ Z)
    (hfixed : ∀ q ∈ D, q.FixedLogBound H)
    (hvars : ∀ u a, a ∈ S u → |(a:ℝ)| ≤ Real.exp H)
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
      A * (∑ q ∈ D, ((q.degreeBudget : ℝ)*α+β*(((Z:ℝ)*H)/Real.log 2))) := by
  have hH0 : 0 ≤ H := (Real.log_pos (by norm_num : (1:ℝ)<2)).le.trans hH
  apply template_family_enlargement_error_le k B₀ V₀ j b s e t D hD i S μ B ν
    α β ((Z:ℝ)*H) A hα hβ (mul_nonneg (Nat.cast_nonneg _) hH0) hA
    hμ hmass hatom hprime hν hνmass hνatom _ r f hf hgood hsupport hfreq
  intro q hq x hx hne
  exact (erased_numerator_log_size_on_support i q hH (hfixed q hq) S hvars x hx hne).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hsyntax q hq) hH0)

end Ostmann.Characters.TemplateSupportRemoval

end

end OAI
