import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Model
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! The moving-cutoff mass estimate yields the fixed half-plane observer.
These are integral comparisons for the actual nonnegative scalar density;
they use neither a maximum of the density nor compact support of the density. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Set MeasureTheory

def upperHalfPlane : Set Plane := {x | 0 < x 1}

theorem upperHalfPlane_measurable : MeasurableSet upperHalfPlane :=
  measurableSet_lt measurable_const (measurable_pi_apply 1)

theorem cutoff_mass_le_observer {ρ φ : Plane → ℝ}
    (hρ : Integrable ρ) (hw : Integrable (fun x => φ x * ρ x))
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, φ x ≤ 1)
    (hzero : ∀ x, x ∉ upperHalfPlane → φ x = 0) :
    (∫ x, φ x * ρ x) ≤ ∫ x in upperHalfPlane, ρ x := by
  rw [← integral_indicator upperHalfPlane_measurable]
  apply integral_mono hw (hρ.indicator upperHalfPlane_measurable)
  intro x
  change φ x * ρ x ≤ upperHalfPlane.indicator ρ x
  by_cases hx : x ∈ upperHalfPlane
  · rw [indicator_of_mem hx]
    exact mul_le_of_le_one_left (hn x) (hb x)
  · rw [indicator_of_notMem hx, hzero x hx, zero_mul]

theorem observer_mass_le_complement_cutoff {ρ φ : Plane → ℝ}
    (hρ : Integrable ρ) (hw : Integrable (fun x => φ x * ρ x))
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, φ x ≤ 1)
    (hzero : ∀ x ∈ upperHalfPlane, φ x = 0) :
    (∫ x in upperHalfPlane, ρ x) ≤ (∫ x, ρ x) - ∫ x, φ x * ρ x := by
  have hi := hρ.indicator upperHalfPlane_measurable
  have he : (∫ x, φ x * ρ x) + (∫ x in upperHalfPlane, ρ x) ≤ ∫ x, ρ x := by
    rw [← integral_indicator upperHalfPlane_measurable, ← integral_add hw hi]
    apply integral_mono (hw.add hi) hρ
    intro x
    change φ x * ρ x + upperHalfPlane.indicator ρ x ≤ ρ x
    by_cases hx : x ∈ upperHalfPlane
    · rw [indicator_of_mem hx, hzero x hx, zero_mul, zero_add]
    · rw [indicator_of_notMem hx, add_zero]
      exact mul_le_of_le_one_left (hn x) (hb x)
  linarith

theorem nonterminal_observer_bound {ρ φ : Plane → ℝ} {δ : ℝ}
    (hρ : Integrable ρ) (hw : Integrable (fun x => φ x * ρ x))
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, φ x ≤ 1)
    (hzero : ∀ x ∈ upperHalfPlane, φ x = 0)
    (hretain : (∫ x, ρ x) - δ ≤ ∫ x, φ x * ρ x) :
    (∫ x in upperHalfPlane, ρ x) ≤ δ := by
  have h := observer_mass_le_complement_cutoff hρ hw hn hb hzero
  linarith

theorem terminal_observer_detects {ρ φ : Plane → ℝ} {δ : ℝ}
    (hρ : Integrable ρ) (hw : Integrable (fun x => φ x * ρ x))
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, φ x ≤ 1)
    (hzero : ∀ x, x ∉ upperHalfPlane → φ x = 0)
    (hm : (∫ x, ρ x) = 1) (hδ : δ < 1 / 2)
    (hretain : (∫ x, ρ x) - δ ≤ ∫ x, φ x * ρ x) :
    1 / 2 < ∫ x in upperHalfPlane, ρ x := by
  have h := cutoff_mass_le_observer hρ hw hn hb hzero
  linarith

end ForcedComputation.ExpandingDetector

end

end OAI
