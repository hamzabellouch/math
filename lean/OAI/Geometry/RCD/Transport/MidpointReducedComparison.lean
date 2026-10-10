import OAI.Geometry.RCD.Transport.MidpointDimensionAlgebra

namespace OAI

/-! # The reduced midpoint coefficient is bounded by the full CD coefficient -/

open Set
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem sigma_negative_midpoint {K N θ : ℝ} (hK : K < 0) (hN : 1 < N) (hθ : 0 < θ) :
    sigma K N (1/2) θ =
      ENNReal.ofReal (1/(2*Real.cosh (θ*Real.sqrt (-K/(N-1))/2))) := by
  rw [sigma_neg_eq hK hN hθ]
  have hz : 0 < θ*Real.sqrt (-K/(N-1)) :=
    mul_pos hθ (Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hK) (sub_pos.mpr hN)))
  rw [show (1/2:ℝ)*θ*Real.sqrt (-K/(N-1)) = (θ*Real.sqrt (-K/(N-1)))/2 by ring,
    sinh_half_div_sinh _ hz]

theorem reduced_midpoint_le_tau_negative {K N θ : ℝ}
    (hK : K < 0) (hN : 1 < N) (hθ : 0 < θ) :
    sigma K (N+1) (1/2) θ ≤ tau K N (1/2) θ := by
  let c := 1-1/N
  let x := θ*Real.sqrt (-K/(N-1))/2
  have hN0 : 0 < N := by linarith
  have hc0 : 0 ≤ c := sub_nonneg.mpr ((div_le_one hN0).mpr hN.le)
  have hc1 : c ≤ 1 := by have := one_div_pos.mpr hN0; dsimp [c]; linarith
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have he : Real.sqrt c*x = θ*Real.sqrt (-K/N)/2 := by
    calc
      _ = θ/2*(Real.sqrt (1-1/N)*Real.sqrt (-K/(N-1))) := by dsimp [x,c]; ring
      _ = _ := by rw [dimension_scaled_sqrt hN]; ring
  have hpow := cosh_dimension_rpow hc0 hc1 hx
  rw [he] at hpow
  rw [sigma_negative_midpoint hK (by linarith : 1 < N+1) hθ,
    show N+1-1=N by ring,
    tau_midpoint_of_sigma (Real.cosh_pos x) (sigma_negative_midpoint hK hN hθ)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = (1/2:ℝ)/Real.cosh (θ*Real.sqrt (-K/N)/2) := by ring
    _ ≤ (1/2:ℝ)/(Real.cosh x)^c :=
      div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos (Real.cosh_pos x) c) hpow

theorem sin_half_div_sin_exact {z : ℝ} (hz : 0 < z) (hzp : z < Real.pi) :
    Real.sin (z/2)/Real.sin z = 1/(2*Real.cos (z/2)) := by
  have hs : Real.sin (z/2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by linarith)
    (by linarith)).ne'
  have hc : Real.cos (z/2) ≠ 0 := (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
    by linarith⟩).ne'
  have he : Real.sin z = 2*Real.sin (z/2)*Real.cos (z/2) := by
    simpa only [show 2*(z/2)=z by ring] using Real.sin_two_mul (z/2)
  rw [he]
  field_simp

theorem sigma_positive_midpoint {K N θ : ℝ} (hK : 0 < K) (hN : 1 < N) (hθ : 0 < θ)
    (hc : θ*Real.sqrt (K/(N-1)) < Real.pi) :
    sigma K N (1/2) θ =
      ENNReal.ofReal (1/(2*Real.cos (θ*Real.sqrt (K/(N-1))/2))) := by
  rw [sigma_pos_eq hK hN hθ hc]
  have hz : 0 < θ*Real.sqrt (K/(N-1)) :=
    mul_pos hθ (Real.sqrt_pos.mpr (div_pos hK (sub_pos.mpr hN)))
  rw [show (1/2:ℝ)*(θ*Real.sqrt (K/(N-1))) = (θ*Real.sqrt (K/(N-1)))/2 by ring,
    sin_half_div_sin_exact hz hc]

theorem reduced_midpoint_le_tau_positive {K N θ : ℝ}
    (hK : 0 < K) (hN : 1 < N) (hθ : 0 < θ)
    (hc : θ*Real.sqrt (K/(N-1)) < Real.pi) :
    sigma K (N+1) (1/2) θ ≤ tau K N (1/2) θ := by
  let c := 1-1/N
  let x := θ*Real.sqrt (K/(N-1))/2
  have hN0 : 0 < N := by linarith
  have hc0 : 0 ≤ c := sub_nonneg.mpr ((div_le_one hN0).mpr hN.le)
  have hc1 : c ≤ 1 := by have := one_div_pos.mpr hN0; dsimp [c]; linarith
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxp : x < Real.pi/2 := by dsimp [x]; linarith
  have he : Real.sqrt c*x = θ*Real.sqrt (K/N)/2 := by
    calc
      _ = θ/2*(Real.sqrt (1-1/N)*Real.sqrt (K/(N-1))) := by dsimp [x,c]; ring
      _ = _ := by rw [dimension_scaled_sqrt hN]; ring
  have hs1 : Real.sqrt c ≤ 1 := by nlinarith [Real.sq_sqrt hc0,Real.sqrt_nonneg c]
  have hred : θ*Real.sqrt (K/N) < Real.pi := by
    have hh : Real.sqrt c*x ≤ x := mul_le_of_le_one_left hx hs1
    rw [he] at hh
    dsimp [x] at hh
    linarith
  have hpow := cos_dimension_rpow hc0 hc1 hx hxp
  rw [he] at hpow
  have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hxp⟩
  have hred' : θ*Real.sqrt (K/(N+1-1)) < Real.pi := by simpa using hred
  rw [sigma_positive_midpoint hK (by linarith : 1 < N+1) hθ hred',
    show N+1-1=N by ring,
    tau_midpoint_of_sigma hcx (sigma_positive_midpoint hK hN hθ hc)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = (1/2:ℝ)/Real.cos (θ*Real.sqrt (K/N)/2) := by ring
    _ ≤ (1/2:ℝ)/(Real.cos x)^c :=
      div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hcx c) hpow

end RegularPointCoordinates

end

end OAI
