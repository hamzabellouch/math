import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartGeometry
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialBudgetAlgebra
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

/-! Quantitative derivatives of an inverse chart from its actual inverse
Jacobian field. The finite-order budget is polynomial in the field's jets. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

def inverseChartJetBudget : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n+1, B => inverseChartJetBudget n B +
      (n.factorial : ℝ)*B*(inverseChartJetBudget n B)^n

lemma inverseChartJetBudget_one_le (n : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    1 ≤ inverseChartJetBudget n B := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpos : 0 ≤ (n.factorial : ℝ)*B*(inverseChartJetBudget n B)^n := by
      have hb := zero_le_one.trans ih
      positivity
    exact ih.trans (le_add_of_nonneg_right hpos)

lemma inverseChartJetBudget_le_succ (n : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    inverseChartJetBudget n B ≤ inverseChartJetBudget (n+1) B := by
  have hb := zero_le_one.trans (inverseChartJetBudget_one_le n hB)
  change _ ≤ _ + _
  exact le_add_of_nonneg_right (by positivity)

lemma inverseChartJetBudget_polynomial (n : ℕ) :
    HasPolynomialBound (inverseChartJetBudget n) := by
  induction n with
  | zero => exact polynomialBound_const zero_le_one
  | succ n ih =>
    exact ih.add (((polynomialBound_const (Nat.cast_nonneg n.factorial)).mul
      polynomialBound_id).mul (ih.pow n))

/-- The derivative equation is the ordinary inverse-function identity. No
bound on the position of the inverse chart is needed for positive jets. -/
theorem inverse_chart_positive_jets
    (e : OpenPartialHomeomorph Base Base)
    (hi : ContDiff ℝ ∞ e.symm) (J : Base → Base →L[ℝ] Base)
    (hJ : ContDiffOn ℝ ∞ J e.source)
    (heq : ∀ y ∈ e.target, fderiv ℝ e.symm y = J (e.symm y))
    {m : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hjets : ∀ k ≤ m, ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ k J e.source x‖ ≤ B) :
    ∀ j, 1 ≤ j → j ≤ m+1 → ∀ y ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target y‖ ≤ inverseChartJetBudget (m+1) B := by
  have hstep : ∀ n ≤ m+1, ∀ j, 1 ≤ j → j ≤ n → ∀ y ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target y‖ ≤ inverseChartJetBudget n B := by
    intro n
    induction n with
    | zero => intro hn j hj hjn; omega
    | succ n ih =>
      intro hn j hj hjn y hy
      by_cases hjold : j ≤ n
      · exact (ih (by omega) j hj hjold y hy).trans (inverseChartJetBudget_le_succ n hB)
      have hjnew : j = n+1 := by omega
      subst j
      have hcomp := norm_iteratedFDerivWithin_comp_le hJ hi.contDiffOn
        (show (n : ℕ∞ω) ≤ ∞ by simp) e.open_source.uniqueDiffOn
        e.open_target.uniqueDiffOn (fun x hx => e.map_target hx) hy
        (fun k hk => hjets k (by omega) _ (e.map_target hy))
        (fun k hk hkn => (ih (by omega) k hk hkn y hy).trans
          (by
            simpa only [pow_one] using
              pow_le_pow_right₀ (inverseChartJetBudget_one_le n hB) hk))
      have heq' : EqOn (fderivWithin ℝ e.symm e.target) (J ∘ e.symm) e.target := by
        intro x hx
        rw [fderivWithin_of_isOpen e.open_target hx]
        exact heq x hx
      rw [← norm_iteratedFDerivWithin_fderivWithin e.open_target.uniqueDiffOn hy,
        iteratedFDerivWithin_congr heq' hy]
      exact hcomp.trans (le_add_of_nonneg_left
        (zero_le_one.trans (inverseChartJetBudget_one_le n hB)))
  exact hstep (m+1) le_rfl

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
