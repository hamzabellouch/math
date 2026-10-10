import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketDifferentiation
import OAI.Analysis.LipschitzHilbert.Packets.PolynomialPacket

namespace OAI

/-! Pointwise multiplier identities for the actual finite planar packet
synthesis. A spatially varying multiplier is frozen at the evaluation
point before using linearity of the finite sum. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketInterval_congr_at (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f g : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (a b : ℕ) (x y : ℝ)
    (h : ∀ j i k, f j i k y x = g j i k y x) :
    planarPacketInterval coeff f a b x y = planarPacketInterval coeff g a b x y := by
  ext k
  simp only [planarPacketInterval, bandIntervalSignal, WithLp.ofLp_toLp,
    scalarBandPartial, planarPacketBand, h]

omit [Fintype κ] in
theorem planarPacketInterval_multiplier_at (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f g : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (M : ℝ → ℝ → ℝ)
    (h : ∀ j i k y x, g j i k y x = (M x y:ℂ)*f j i k y x)
    (a b : ℕ) (x y : ℝ) :
    planarPacketInterval coeff g a b x y = (M x y) • planarPacketInterval coeff f a b x y := by
  rw [← planarPacketInterval_smul coeff f (M x y) a b x y]
  apply planarPacketInterval_congr_at
  exact fun j i k => h j i k y x

theorem planarPacketInterval_multiplier_norm (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f g : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (M : ℝ → ℝ → ℝ)
    (hM : ∀ x y, 0 ≤ M x y)
    (h : ∀ j i k y x, g j i k y x = (M x y:ℂ)*f j i k y x)
    (a b : ℕ) (x y : ℝ) :
    ‖planarPacketInterval coeff g a b x y‖ =
      M x y*‖planarPacketInterval coeff f a b x y‖ := by
  rw [planarPacketInterval_multiplier_at coeff f g M h, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (hM x y)]

end LipschitzHilbert

end

end OAI
