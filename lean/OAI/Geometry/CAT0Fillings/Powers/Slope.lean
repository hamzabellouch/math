import Mathlib
import OAI.Geometry.CAT0Fillings.Powers.Truncated

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.ClosedCalculus

lemma truncatedPower_le_power {γ N t : ℝ} (hγ : 1 < γ) (hN : 0 < N) (ht : 0 ≤ t) :
    truncatedPower γ N t ≤ t^γ := by
  by_cases htN : t ≤ N
  · exact le_of_eq (truncatedPower_of_le hγ ht htN)
  · have htpos : 0 < t := hN.trans (lt_of_not_ge htN)
    rw [truncatedPower_of_ge ht (le_of_not_ge htN)]
    have hh := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN.le (le_of_not_ge htN) (by linarith : 0 ≤ γ-1)) ht
    apply hh.trans_eq
    simpa only [truncatedPower,max_eq_left ht,min_self] using (truncatedPower_of_le hγ ht (le_refl t))

lemma truncatedPower_le_linear {γ N t : ℝ} (hγ : 1 < γ) (hN : 0 < N) (ht : 0 ≤ t) :
    truncatedPower γ N t ≤ t*N^(γ-1) := by
  rw [truncatedPower_of_nonneg ht]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_min ht hN.le) (min_le_right _ _) (by linarith)) ht

lemma truncatedPower_product {γ N t : ℝ} (hγ : 1 < γ) (hN : 0 < N) (ht : 0 ≤ t) :
    t*truncatedPower (2*γ-1) N t = (truncatedPower γ N t)^2 := by
  rw [truncatedPower_of_nonneg ht,truncatedPower_of_nonneg ht]
  have he : 2*γ-1-1 = (γ-1)+(γ-1) := by ring
  rw [he, Real.rpow_add_of_nonneg (le_min ht hN.le)
    (sub_nonneg.mpr hγ.le) (sub_nonneg.mpr hγ.le)]
  ring

lemma truncatedPower_rhs {γ N t p : ℝ} (hγ : 1 < γ) (hN : 0 < N) (ht : 0 ≤ t) (hp : 2 < p) :
    t^(p-1)*truncatedPower (2*γ-1) N t = t^(p-2)*(truncatedPower γ N t)^2 := by
  rw [←truncatedPower_product hγ hN ht]
  by_cases ht0 : t = 0
  · simp only [ht0,Real.zero_rpow (by linarith : p-1 ≠ 0),zero_mul,mul_zero]
  · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have he : t^(p-1) = t^(p-2)*t := by
      calc
        t^(p-1) = t^((p-2)+1) := by congr 1; ring
        _ = t^(p-2)*t^(1:ℝ) := Real.rpow_add htp _ _
        _ = t^(p-2)*t := by rw [Real.rpow_one]
    rw [he,mul_assoc]

lemma power_ratio_pos {γ : ℝ} (hγ : 1 < γ) : 0 < (2*γ-1)/γ^2 :=
  div_pos (by linarith) (sq_pos_of_pos (by linarith))

lemma power_ratio_le_one {γ : ℝ} (hγ : 1 < γ) : (2*γ-1)/γ^2 ≤ 1 := by
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < γ))).mpr
  nlinarith [sq_nonneg (γ-1)]

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus

lemma truncatedPowerSlope_nonneg {γ N t : ℝ} (hγ : 1 < γ) (hN : 0 < N) (ht : 0 ≤ t) :
    0 ≤ truncatedPowerSlope γ N t := by
  dsimp [truncatedPowerSlope]
  split_ifs
  · exact mul_nonneg (by linarith) (Real.rpow_nonneg ht _)
  · exact Real.rpow_nonneg hN.le _

lemma truncatedPowerSlope_le {γ N t : ℝ} (hγ : 1 < γ) (hN : 0 < N) (ht : 0 ≤ t) :
    truncatedPowerSlope γ N t ≤ γ*t^(γ-1) := by
  dsimp [truncatedPowerSlope]
  split_ifs with h
  · exact le_rfl
  · have hh := Real.rpow_le_rpow hN.le (le_of_not_gt h) (by linarith : 0 ≤ γ-1)
    have hp := Real.rpow_nonneg ht (γ-1)
    nlinarith

lemma truncatedPowerSlope_ratio {γ N t : ℝ} (hγ : 1 < γ) (hN : 0 < N) (ht : 0 ≤ t) :
    (2*γ-1)/γ^2*(truncatedPowerSlope γ N t)^2 ≤ truncatedPowerSlope (2*γ-1) N t := by
  have he : 2*γ-1-1 = (γ-1)*2 := by ring
  have hg0 : γ ≠ 0 := by linarith
  dsimp [truncatedPowerSlope]
  split_ifs with h
  · rw [he,Real.rpow_mul ht,Real.rpow_two,mul_pow]
    have hg2 : γ^2 ≠ 0 := pow_ne_zero _ hg0
    rw [←mul_assoc,div_mul_cancel₀ _ hg2]
  · rw [he,Real.rpow_mul hN.le,Real.rpow_two]
    exact mul_le_of_le_one_left (sq_nonneg _) (power_ratio_le_one hγ)

lemma truncatedPower_tendsto {γ t : ℝ} (hγ : 1 < γ) (ht : 0 ≤ t) :
    Tendsto (fun j : ℕ => truncatedPower γ ((j:ℝ)+1) t) atTop (𝓝 (t^γ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j:ℝ)) atTop atTop).eventually (eventually_ge_atTop t)] with j hj
  exact (truncatedPower_of_le hγ ht (by linarith)).symm

lemma truncatedPowerSlope_tendsto {γ t : ℝ} :
    Tendsto (fun j : ℕ => truncatedPowerSlope γ ((j:ℝ)+1) t) atTop (𝓝 (γ*t^(γ-1))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j:ℝ)) atTop atTop).eventually (eventually_ge_atTop t)] with j hj
  rw [truncatedPowerSlope,ite_eq_left (by linarith)]

end CAT0Fillings.ClosedCalculus
end

end OAI
