import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Frozen-direction sampling

The sampling maps and positive-time representation of the short Hilbert transform
in §1 of *A uniform Hilbert transform estimate for Lipschitz directions*.
The direction in these definitions is evaluated at the output point.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace LipschitzHilbert

abbrev DirectionPlane := EuclideanSpace ℝ (Fin 2)

/-- Sampling along the straight line through the output point. -/
def sample (v : DirectionPlane → DirectionPlane) (t : ℝ) (x : DirectionPlane) :
    DirectionPlane := x - t • v x

/-- The positive-time, symmetrized short directional Hilbert transform. -/
def shortTransform (v : DirectionPlane → DirectionPlane) (ε a : ℝ)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) : ℂ :=
  ∫ t in ε..a, t⁻¹ • (f (sample v t x) - f (sample v (-t) x))

theorem sample_sub (v : DirectionPlane → DirectionPlane) (t : ℝ)
    (x y : DirectionPlane) :
    sample v t x - sample v t y = (x - y) - t • (v x - v y) := by
  simp only [sample, smul_sub]
  abel

/-- The elementary upper distortion estimate used before changing variables. -/
theorem sample_dist_le {v : DirectionPlane → DirectionPlane} {K : ℝ≥0}
    (hv : LipschitzWith K v) (t : ℝ) (x y : DirectionPlane) :
    dist (sample v t x) (sample v t y) ≤
      (1 + |t| * (K : ℝ)) * dist x y := by
  rw [dist_eq_norm, sample_sub]
  calc
    ‖(x - y) - t • (v x - v y)‖ ≤ ‖x - y‖ + ‖t • (v x - v y)‖ :=
      norm_sub_le _ _
    _ = dist x y + |t| * dist (v x) (v y) := by
      simp only [norm_smul, Real.norm_eq_abs, dist_eq_norm]
    _ ≤ dist x y + |t| * ((K : ℝ) * dist x y) := by
      gcongr
      exact hv.dist_le_mul x y
    _ = (1 + |t| * (K : ℝ)) * dist x y := by ring

/-- The lower distortion estimate; it has content when `|t| K < 1`. -/
theorem sample_dist_ge {v : DirectionPlane → DirectionPlane} {K : ℝ≥0}
    (hv : LipschitzWith K v) (t : ℝ) (x y : DirectionPlane) :
    (1 - |t| * (K : ℝ)) * dist x y ≤ dist (sample v t x) (sample v t y) := by
  have htri : dist x y ≤ dist (sample v t x) (sample v t y) +
      |t| * dist (v x) (v y) := by
    simp only [dist_eq_norm, sample_sub]
    calc
      ‖x - y‖ = ‖((x - y) - t • (v x - v y)) + t • (v x - v y)‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖(x - y) - t • (v x - v y)‖ + ‖t • (v x - v y)‖ := norm_add_le _ _
      _ = _ := by simp only [norm_smul, Real.norm_eq_abs]
  have hmul := mul_le_mul_of_nonneg_left (hv.dist_le_mul x y) (abs_nonneg t)
  nlinarith

theorem sample_injective {v : DirectionPlane → DirectionPlane} {K : ℝ≥0}
    (hv : LipschitzWith K v) {t : ℝ} (ht : |t| * (K : ℝ) < 1) :
    Function.Injective (sample v t) := by
  intro x y hxy
  have h := sample_dist_ge hv t x y
  rw [hxy, dist_self] at h
  have hd : dist x y ≤ 0 := by
    nlinarith [dist_nonneg (x := x) (y := y)]
  exact dist_le_zero.mp hd

/-- The usual reciprocal-Lipschitz normalization of a vector field. -/
def rescaleField (L : ℝ) (v : DirectionPlane → DirectionPlane) :
    DirectionPlane → DirectionPlane := fun x => v (L⁻¹ • x)

def rescaleFunction (L : ℝ) (f : DirectionPlane → ℂ) :
    DirectionPlane → ℂ := fun x => f (L⁻¹ • x)

theorem sample_rescale {L : ℝ} (hL : L ≠ 0)
    (v : DirectionPlane → DirectionPlane) (t : ℝ) (x : DirectionPlane) :
    sample (rescaleField L v) (L * t) (L • x) = L • sample v t x := by
  simp [sample, rescaleField, smul_sub, smul_smul, hL]

theorem rescaleField_unit {L : ℝ} (v : DirectionPlane → DirectionPlane)
    (hv : ∀ x, ‖v x‖ = 1) : ∀ x, ‖rescaleField L v x‖ = 1 :=
  fun x => hv (L⁻¹ • x)

theorem rescaleField_lipschitz {L : ℝ} (hL : 0 < L)
    {v : DirectionPlane → DirectionPlane} (hv : LipschitzWith ⟨L, hL.le⟩ v) :
    LipschitzWith 1 (rescaleField L v) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (rescaleField L v x) (rescaleField L v y) ≤
        L * dist (L⁻¹ • x) (L⁻¹ • y) := hv.dist_le_mul _ _
    _ = dist x y := by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
      field_simp
    _ = (1 : ℝ≥0) * dist x y := by simp

/-- Dilation intertwines the two hard truncation endpoints exactly. -/
theorem shortTransform_rescale {L : ℝ} (hL : L ≠ 0)
    (v : DirectionPlane → DirectionPlane) (ε a : ℝ)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) :
    shortTransform (rescaleField L v) (L * ε) (L * a) (rescaleFunction L f) (L • x) =
      shortTransform v ε a f x := by
  let g : ℝ → ℂ := fun s => s⁻¹ •
    (rescaleFunction L f (sample (rescaleField L v) s (L • x)) -
      rescaleFunction L f (sample (rescaleField L v) (-s) (L • x)))
  have hg (t : ℝ) : g (L * t) = L⁻¹ •
      (t⁻¹ • (f (sample v t x) - f (sample v (-t) x))) := by
    dsimp [g]
    rw [show -(L * t) = L * (-t) by ring, sample_rescale hL,
      sample_rescale hL]
    simp [rescaleFunction, smul_smul, hL, mul_inv_rev, mul_comm, mul_assoc]
  change (∫ s in L * ε..L * a, g s) = _
  rw [← intervalIntegral.smul_integral_comp_mul_left g L]
  simp_rw [hg]
  rw [intervalIntegral.integral_smul, smul_smul, mul_inv_cancel₀ hL, one_smul]
  rfl

end LipschitzHilbert

end

end OAI
