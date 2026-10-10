import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGap

namespace OAI

noncomputable section
namespace Ostmann.Characters
open Filter
open scoped Topology BigOperators

theorem eventually_scale_gap_finite_sum (C z : ℝ) (d : ℕ) {α δ : ℝ}
    (hz : 0 ≤ z) (hα : 0 < α) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ {ι : Type} [Fintype ι] (f : ι → ℂ),
      (Fintype.card ι : ℝ) ≤ Real.exp (historyPolynomialCost C z d L) →
      (∀ i, ‖f i‖ ≤ Real.exp (-δ*Real.exp (α*L))) →
      ‖∑ i, f i‖ ≤ Real.exp (-(δ/2)*Real.exp (α*L)) := by
  filter_upwards [eventually_historyPolynomialCost_le C z d hz hα (half_pos hδ)] with L hL
  intro ι _ f hcard hf
  calc
    _ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, Real.exp (-δ*Real.exp (α*L)) := Finset.sum_le_sum (fun i _ => hf i)
    _ = (Fintype.card ι : ℝ)*Real.exp (-δ*Real.exp (α*L)) := by simp
    _ ≤ Real.exp (historyPolynomialCost C z d L)*Real.exp (-δ*Real.exp (α*L)) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = Real.exp (historyPolynomialCost C z d L-δ*Real.exp (α*L)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Ostmann.Characters

end

end OAI
