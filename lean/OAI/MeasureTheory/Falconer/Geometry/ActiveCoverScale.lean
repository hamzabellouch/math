import OAI.MeasureTheory.Falconer.Slicing.GaussianLossAbsorption

namespace OAI

/-! # The original tube count after codimension-h slicing -/

namespace Falconer

theorem gaussian_active_cover_scale {δ ε κ q Nc D : ℝ} (h : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hεκ : ε ≤ κ) (hD : 0 ≤ D)
    (hNc : Nc ≤ δ^(-q-ε)) :
    (δ^(-κ))^11*(Nc*(2*(D*δ))^h) ≤
      (2*D)^h*(δ^(-κ))^12*δ^(-(q-(h:ℝ))) := by
  have hε : δ^(-ε) ≤ δ^(-κ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hεκ)
  have hpower : δ^(-q-ε)*δ^h = δ^(-ε)*δ^(-(q-(h:ℝ))) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hδ,← Real.rpow_add hδ]
    congr 1
    ring
  calc
    _ ≤ (δ^(-κ))^11*(δ^(-q-ε)*(2*(D*δ))^h) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNc (by positivity)) (by positivity)
    _ = (2*D)^h*(δ^(-κ))^11*(δ^(-ε)*δ^(-(q-(h:ℝ)))) := by
      rw [show 2*(D*δ) = (2*D)*δ by ring,mul_pow]
      calc
        _ = (2*D)^h*(δ^(-κ))^11*(δ^(-q-ε)*δ^h) := by ring
        _ = _ := by rw [hpower]
    _ ≤ (2*D)^h*(δ^(-κ))^11*(δ^(-κ)*δ^(-(q-(h:ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hε (Real.rpow_nonneg hδ.le _)) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
