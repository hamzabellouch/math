import OAI.Geometry.RCD.Coordinates.FrozenJetTransport
import OAI.Geometry.RCD.Coordinates.NormalizedUpdate
import OAI.Geometry.RCD.Coordinates.DifferentialStep

namespace OAI

/-! # Directional cutoff bounds from its actual normalized jets -/

open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Undo the frozen affine source in any derivative order. -/
theorem frozen_cutoff_directional_bound (T : E ≃L[ℝ] E) (phi : E → ℝ)
    (x v : E) {r W : ℝ} (hr : 0 < r) (m : ℕ) (hphi : ContDiffAt ℝ m phi x)
    (hjet : ‖iteratedFDeriv ℝ m (fun z => phi (frozenSource r T x z)) 0‖ ≤ W) :
    r ^ m * ‖iteratedFDeriv ℝ m phi x (fun _ => v)‖ ≤ W * ‖T v‖ ^ m := by
  let L : E →L[ℝ] E := r • T.symm.toContinuousLinearMap
  have hf : ContDiffAt ℝ m phi (x + L 0) := by simpa using hphi
  have hc := iteratedFDeriv_comp_affine_apply L phi x 0 m hf (fun _ => T v)
  have harg : (fun _ : Fin m => L (T v)) = fun _ => r • v := by
    funext j
    simp [L]
  rw [harg, (iteratedFDeriv ℝ m phi (x + L 0)).map_smul_univ] at hc
  simp only [map_zero, add_zero] at hc
  change iteratedFDeriv ℝ m (fun z => phi (frozenSource r T x z)) 0 (fun _ => T v) = _ at hc
  have hn := (iteratedFDeriv ℝ m (fun z => phi (frozenSource r T x z)) 0).le_opNorm
    (fun _ => T v)
  calc
    _ = ‖iteratedFDeriv ℝ m (fun z => phi (frozenSource r T x z)) 0 (fun _ => T v)‖ := by
      rw [hc]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr.le _)]
    _ ≤ ‖iteratedFDeriv ℝ m (fun z => phi (frozenSource r T x z)) 0‖ * ‖T v‖ ^ m := by
      simpa using hn
    _ ≤ W * ‖T v‖ ^ m := mul_le_mul_of_nonneg_right hjet (by positivity)

/-- The first two orders of one Gevrey estimate supply exactly the
directional hypotheses used by the finite patch-field calculus. -/
theorem frozen_cutoff_first_second (T : E ≃L[ℝ] E) (phi : E → ℝ)
    (x v : E) {r L : ℝ} (hr : 0 < r) (hL : 0 ≤ L) (hphi : ContDiffAt ℝ 2 phi x)
    (hjet : ∀ m : ℕ, ‖iteratedFDeriv ℝ m (fun z => phi (frozenSource r T x z)) 0‖ ≤
      L ^ (m + 1) * (m.factorial : ℝ) ^ 2) :
    |fderiv ℝ phi x v| ≤ (L ^ 2 + 4 * L ^ 3) / r * ‖T v‖ ∧
    |diagonalSecond phi x v| ≤ (L ^ 2 + 4 * L ^ 3) / r ^ 2 * ‖T v‖ ^ 2 := by
  have h1 := frozen_cutoff_directional_bound T phi x v hr 1
    (hphi.of_le (by norm_num)) (hjet 1)
  have h2 := frozen_cutoff_directional_bound T phi x v hr 2 hphi (hjet 2)
  simp only [iteratedFDeriv_one_apply, Real.norm_eq_abs, pow_one, Nat.factorial_one,
    Nat.cast_one, one_pow, mul_one] at h1
  norm_num only [Nat.add_one_sub_one, Nat.reduceAdd] at h1
  rw [← diagonalSecond_eq hphi] at h2
  norm_num only [Nat.factorial_two, Nat.cast_ofNat, Real.norm_eq_abs] at h2
  constructor
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hr).2
    linarith only [h1, show 0 ≤ 4 * L ^ 3 * ‖T v‖ by positivity]
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hr)).2
    linarith only [h2, show 0 ≤ L ^ 2 * ‖T v‖ ^ 2 by positivity]

end RegularPointCoordinates

end

end OAI
