import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketLocality

namespace OAI

/-! Remove the coefficient normalization after the packet concentration
estimate, preserving the original integral-defined analyzing coefficients. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketInterval_coeff_smul (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (s : ℝ) (a b : ℕ) (x y : ℝ) :
    planarPacketInterval (fun j i => s • coeff j i) wave a b x y =
      s • planarPacketInterval coeff wave a b x y := by
  rw [← planarPacketInterval_smul coeff wave s a b x y]
  have hb (j : Fin N) (k : κ) (y : ℝ) :
      planarPacketBand (fun j i => s • coeff j i) wave j k x y =
        planarPacketBand coeff (fun j i k t z => (s:ℂ)*wave j i k t z) j k x y := by
    apply Finset.sum_congr rfl
    intro i _
    change ((s:ℂ)*coeff j i k)*wave j i k y x = coeff j i k*((s:ℂ)*wave j i k y x)
    ring
  ext k
  simp only [planarPacketInterval, bandIntervalSignal, WithLp.ofLp_toLp, scalarBandPartial, hb]

theorem planarPacketInterval_denormalize_bound (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (C B : ℝ) (hC : 0 < C)
    (a b : ℕ) (x y : ℝ)
    (h : ‖planarPacketInterval (fun j i => C⁻¹ • coeff j i) wave a b x y‖ ≤ B) :
    ‖planarPacketInterval coeff wave a b x y‖ ≤ C*B := by
  rw [planarPacketInterval_coeff_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hC)] at h
  have hh := mul_le_mul_of_nonneg_left h hC.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] using hh

end LipschitzHilbert

end

end OAI
