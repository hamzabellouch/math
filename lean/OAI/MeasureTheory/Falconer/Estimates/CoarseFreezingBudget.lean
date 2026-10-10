import OAI.MeasureTheory.Falconer.Geometry.ProjectionSampleBudget

namespace OAI

/-! The fixed polynomial losses in coarse pencil uniformization and
fine-packet freezing, before the common exponential absorption. -/
namespace Falconer

theorem coarse_comparable_size_bound {ρ κ s t K L m D : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) (_hs : 0 ≤ s) (hs1 : s ≤ 1) (hgap : κ ≤ t-s)
    (hD : 80 ≤ D) (hK : 0 ≤ K) (hKD : K ≤ D^6)
    (_hL : 0 ≤ L) (hLD : L ≤ D/(ρ^s)^2) (hH : projectionGapConstant κ ≤ D)
    (hm : m ≤ 2*L*K*(80*ρ)^s*(1+K*planarPotentialConstant s t)) :
    2*m ≤ D^20/ρ^s := by
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hρs : 0 < ρ^s := Real.rpow_pos_of_pos hρ _
  have hst : s < t := by linarith only [hκ,hgap]
  have hp := planarPotentialConstant_pos hst
  have hpD : planarPotentialConstant s t ≤ D := (planarPotentialConstant_gap hκ hs1 hgap).trans hH
  have hD7 : 1 ≤ D^7 := one_le_pow₀ hD1
  have h80 : (80:ℝ)^s ≤ 80 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 80) hs1
  have hpot : 1+K*planarPotentialConstant s t ≤ 2*D^7 := by
    calc
      _ ≤ 1+D^6*D := by gcongr
      _ ≤ _ := by nlinarith only [hD7]
  have h640 : 640 ≤ D^6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 80) hD 6
    norm_num at hh
    linarith only [hh]
  calc
    2*m ≤ 2*(2*L*K*(80*ρ)^s*(1+K*planarPotentialConstant s t)) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = 4*L*K*((80:ℝ)^s*ρ^s)*(1+K*planarPotentialConstant s t) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hρ.le]
      ring
    _ ≤ 4*(D/(ρ^s)^2)*D^6*(80*ρ^s)*(2*D^7) := by gcongr
    _ = 640*D^14/ρ^s := by field_simp; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hρs.le
      calc
        _ ≤ D^6*D^14 := mul_le_mul_of_nonneg_right h640 (pow_nonneg hD0 _)
        _ = _ := by ring

theorem coarse_freezing_loss {ρ s D m M J K : ℝ}
    (hρ : 0 < ρ) (hD : 80 ≤ D) (hm : 0 < m) (hM : 0 ≤ M) (hJ : 0 < J)
    (hmD : 1/(D^5*ρ^s) ≤ m) (hMD : M ≤ D^20/ρ^s) (hJD : J ≤ D)
    (_hK : 0 ≤ K) (hKD : K ≤ D^6) :
    2*J*M/m ≤ D^27 ∧ K*(2*J*M/m) ≤ D^33 ∧
      1/(D^7*ρ^s) ≤ m/(2*J) := by
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hρs : 0 < ρ^s := Real.rpow_pos_of_pos hρ _
  have hF : 2*J*M/m ≤ D^27 := by
    calc
      _ ≤ 2*D*(D^20/ρ^s)/(1/(D^5*ρ^s)) := by gcongr
      _ = 2*D^26 := by field_simp
      _ ≤ D*D^26 := mul_le_mul_of_nonneg_right (by linarith only [hD]) (pow_nonneg hD0 _)
      _ = _ := by ring
  refine ⟨hF,?_,?_⟩
  · calc
      _ ≤ D^6*D^27 := mul_le_mul hKD hF (by positivity) (pow_nonneg hD0 _)
      _ = _ := by ring
  · calc
      _ ≤ (1/(D^5*ρ^s))/(2*D) := by
        rw [div_div]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have hh : 2*D ≤ D^2 := by nlinarith only [hD,hD0]
        calc
          _ = (2*D)*(D^5*ρ^s) := by ring
          _ ≤ D^2*(D^5*ρ^s) := mul_le_mul_of_nonneg_right hh (by positivity)
          _ = _ := by ring
      _ ≤ m/(2*J) := by gcongr

theorem coarse_weight_scale_bound {Δ s B D : ℝ}
    (hΔ : 0 < Δ) (hs1 : s ≤ 1) (hD : 80 ≤ D)
    (hB : B ≤ D^20/(Δ/8)^s) : B ≤ D^21/Δ^s := by
  have hD0 : 0 ≤ D := by linarith only [hD]
  have hΔs : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have h8 : (8:ℝ)^s ≤ D := by
    have hh : (8:ℝ)^s ≤ 8 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 8) hs1
    exact hh.trans (by linarith only [hD])
  calc
    B ≤ D^20/(Δ/8)^s := hB
    _ = D^20*(8:ℝ)^s/Δ^s := by
      rw [Real.div_rpow hΔ.le (by norm_num : (0:ℝ) ≤ 8),div_div_eq_mul_div]
    _ ≤ D^20*D/Δ^s := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left h8 (pow_nonneg hD0 _)) hΔs.le
    _ = _ := by ring

end Falconer

end OAI
