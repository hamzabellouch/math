import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Stability of the removed scalar phase

The dominant-path comparison in §9 removes the scalar phase of its path
weight. Relative motion of a nonzero complex weight gives controlled motion
of that phase, and hence of the rotated off-path vector.
-/

noncomputable section

namespace LipschitzHilbert

section Normalize

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Unit-vector normalization has a two-over-the-reference-norm bound. -/
theorem normalize_motion (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖NormedSpace.normalize y - NormedSpace.normalize x‖ ≤ 2 * ‖y - x‖ / ‖x‖ := by
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have heq : ‖x‖ • (NormedSpace.normalize y - NormedSpace.normalize x) =
      (y - x) + (‖x‖ - ‖y‖) • NormedSpace.normalize y := by
    simp only [smul_sub, sub_smul, NormedSpace.norm_smul_normalize]
    abel
  have hnorm : ‖x‖ * ‖NormedSpace.normalize y - NormedSpace.normalize x‖ ≤ 2 * ‖y - x‖ := by
    calc
      _ = ‖‖x‖ • (NormedSpace.normalize y - NormedSpace.normalize x)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hxnorm]
      _ ≤ ‖y - x‖ + ‖(‖x‖ - ‖y‖) • NormedSpace.normalize y‖ := by rw [heq]; exact norm_add_le _ _
      _ = ‖y - x‖ + |‖x‖ - ‖y‖| := by
        rw [norm_smul, Real.norm_eq_abs, NormedSpace.norm_normalize hy, mul_one]
      _ ≤ ‖y - x‖ + ‖y - x‖ := by
        exact add_le_add_right (by simpa only [norm_sub_rev] using abs_norm_sub_norm_le x y) _
      _ = _ := by ring
  apply (le_div_iff₀ hxnorm).2
  nlinarith

end Normalize

/-- The unit complex phase of a weight. -/
def scalarPhase (z : ℂ) : ℂ := NormedSpace.normalize z

theorem scalarPhase_eq_div (z : ℂ) : scalarPhase z = z / (‖z‖ : ℂ) := by
  simp only [scalarPhase, NormedSpace.normalize, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem norm_scalarPhase {z : ℂ} (hz : z ≠ 0) : ‖scalarPhase z‖ = 1 :=
  NormedSpace.norm_normalize hz

theorem scalarPhase_ne_zero {z : ℂ} (hz : z ≠ 0) : scalarPhase z ≠ 0 := by
  intro h
  have hn := norm_scalarPhase hz
  rw [h, norm_zero] at hn
  norm_num at hn

/-- A relative complex-weight perturbation less than one preserves its
nonzero value and moves its unit phase by at most twice that perturbation. -/
theorem scalarPhase_relative_motion {z z' : ℂ} {ε : ℝ}
    (hz : z ≠ 0) (hε : ε < 1) (hmotion : ‖z' - z‖ ≤ ε * ‖z‖) :
    z' ≠ 0 ∧ ‖scalarPhase z' - scalarPhase z‖ ≤ 2 * ε := by
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hz' : z' ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg] at hmotion
    nlinarith
  refine ⟨hz', ?_⟩
  have h := normalize_motion z z' hz hz'
  change ‖scalarPhase z' - scalarPhase z‖ ≤ 2 * ‖z' - z‖ / ‖z‖ at h
  refine h.trans ?_
  apply (div_le_iff₀ hznorm).2
  nlinarith

theorem scalarPhase_inverse_motion {z z' : ℂ} {ε : ℝ}
    (hz : z ≠ 0) (hε : ε < 1) (hmotion : ‖z' - z‖ ≤ ε * ‖z‖) :
    ‖(scalarPhase z')⁻¹ - (scalarPhase z)⁻¹‖ ≤ 2 * ε := by
  obtain ⟨hz', hphase⟩ := scalarPhase_relative_motion hz hε hmotion
  have h := dist_inv_inv₀ (scalarPhase_ne_zero hz') (scalarPhase_ne_zero hz)
  simp only [norm_scalarPhase hz', norm_scalarPhase hz, one_mul, div_one, dist_eq_norm] at h
  rw [h]
  exact hphase

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Removing moving unit scalar phases costs only phase motion times the
size of the off-path vector, in addition to its own motion. -/
theorem rotated_off_path_motion {z z' : ℂ} {ε K u : ℝ}
    (hz : z ≠ 0) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hweight : ‖z' - z‖ ≤ ε * ‖z‖) (X X' : E)
    (hX : ‖X‖ ≤ K * u) (hmove : ‖X' - X‖ ≤ ε * K * u) :
    ‖(scalarPhase z')⁻¹ • X' - (scalarPhase z)⁻¹ • X‖ ≤ 3 * ε * K * u := by
  obtain ⟨hz', _⟩ := scalarPhase_relative_motion hz hε1 hweight
  have hphase := scalarPhase_inverse_motion hz hε1 hweight
  have heq : (scalarPhase z')⁻¹ • X' - (scalarPhase z)⁻¹ • X =
      (scalarPhase z')⁻¹ • (X' - X) +
        ((scalarPhase z')⁻¹ - (scalarPhase z)⁻¹) • X := by
    simp only [smul_sub, sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖(scalarPhase z')⁻¹ • (X' - X)‖ +
        ‖((scalarPhase z')⁻¹ - (scalarPhase z)⁻¹) • X‖ := norm_add_le _ _
    _ = ‖X' - X‖ + ‖(scalarPhase z')⁻¹ - (scalarPhase z)⁻¹‖ * ‖X‖ := by
      rw [norm_smul, norm_inv, norm_scalarPhase hz', inv_one, one_mul, norm_smul]
    _ ≤ ε * K * u + (2 * ε) * (K * u) :=
      add_le_add hmove (mul_le_mul hphase hX (norm_nonneg _) (mul_nonneg (by norm_num) hε0))
    _ = _ := by ring

end Rotation

end LipschitzHilbert

end

end OAI
