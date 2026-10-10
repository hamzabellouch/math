import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingMovingCutoff
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingObservation

namespace OAI

/-! The concrete concentration cutoffs retain their mass when the radius
doubles, and place that mass on the required side of the fixed observer. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Set MeasureTheory

theorem concentrationCutoff_le_doubled {R R' : ℝ} (hR : 0 < R) (hRR : 2 * R ≤ R')
    (c x : Plane) : concentrationCutoff R c x ≤ concentrationCutoff R' c x := by
  by_cases hx : concentrationCutoff R c x = 0
  · rw [hx]
    exact (concentrationCutoff_range R' c x).1
  · have hR' : 0 < R' := by linarith
    have hb := concentrationCutoff_support hR c hx
    have he : concentrationCutoff R' c x = 1 := concentrationCutoff_one hR' (fun j => by
      have hj := hb j
      linarith)
    rw [he]
    exact (concentrationCutoff_range R c x).2

theorem concentrationCutoff_integrable {ρ : Plane → ℝ} (hρ : Integrable ρ)
    (R : ℝ) (c : Plane) : Integrable (fun x => concentrationCutoff R c x * ρ x) := by
  apply hρ.bdd_mul (concentrationCutoff_smooth R c).continuous.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (concentrationCutoff_range R c x).1]
  exact (concentrationCutoff_range R c x).2

theorem concentration_mass_le_doubled {ρ : Plane → ℝ} (hρ : Integrable ρ)
    (hn : ∀ x, 0 ≤ ρ x) {R R' : ℝ} (hR : 0 < R) (hRR : 2 * R ≤ R') (c : Plane) :
    (∫ x, concentrationCutoff R c x * ρ x) ≤
      ∫ x, concentrationCutoff R' c x * ρ x := by
  apply integral_mono (concentrationCutoff_integrable hρ R c)
    (concentrationCutoff_integrable hρ R' c)
  intro x
  exact mul_le_mul_of_nonneg_right (concentrationCutoff_le_doubled hR hRR c x) (hn x)

theorem concentrationCutoff_zero_on_upper {R : ℝ} (hR : 0 < R) {c : Plane}
    (hc : c 1 ≤ -R) {x : Plane} (hx : x ∈ upperHalfPlane) :
    concentrationCutoff R c x = 0 := by
  by_contra hn
  have hb := concentrationCutoff_support hR c hn 1
  have hxu : 0 < x 1 := hx
  linarith [(le_abs_self (x 1 - c 1)).trans hb]

theorem concentrationCutoff_zero_off_upper {R : ℝ} (hR : 0 < R) {c : Plane}
    (hc : R < c 1) {x : Plane} (hx : x ∉ upperHalfPlane) :
    concentrationCutoff R c x = 0 := by
  by_contra hn
  have hb := concentrationCutoff_support hR c hn 1
  have hxu : x 1 ≤ 0 := le_of_not_gt hx
  linarith [neg_le_abs (x 1 - c 1)]

theorem concentration_nonterminal_observer {ρ : Plane → ℝ} (hρ : Integrable ρ)
    (hn : ∀ x, 0 ≤ ρ x) {R δ : ℝ} (hR : 0 < R) {c : Plane} (hc : c 1 ≤ -R)
    (hr : (∫ x, ρ x) - δ ≤ ∫ x, concentrationCutoff R c x * ρ x) :
    (∫ x in upperHalfPlane, ρ x) ≤ δ :=
  nonterminal_observer_bound hρ (concentrationCutoff_integrable hρ R c) hn
    (fun x => (concentrationCutoff_range R c x).2)
    (fun _ hx => concentrationCutoff_zero_on_upper hR hc hx) hr

theorem concentration_terminal_observer {ρ : Plane → ℝ} (hρ : Integrable ρ)
    (hn : ∀ x, 0 ≤ ρ x) {R δ : ℝ} (hR : 0 < R) {c : Plane} (hc : R < c 1)
    (hm : (∫ x, ρ x) = 1) (hδ : δ < 1 / 2)
    (hr : (∫ x, ρ x) - δ ≤ ∫ x, concentrationCutoff R c x * ρ x) :
    1 / 2 < ∫ x in upperHalfPlane, ρ x :=
  terminal_observer_detects hρ (concentrationCutoff_integrable hρ R c) hn
    (fun x => (concentrationCutoff_range R c x).2)
    (fun _ hx => concentrationCutoff_zero_off_upper hR hc hx) hm hδ hr

end ForcedComputation.ExpandingDetector

end

end OAI
