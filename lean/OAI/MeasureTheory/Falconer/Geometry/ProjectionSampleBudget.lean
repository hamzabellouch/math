import OAI.MeasureTheory.Falconer.Geometry.RobustProjectionSets

namespace OAI

/-! Uniform polynomial costs for the robust projection step. These bounds
keep every loss explicit before the dyadic exponential absorption. -/
namespace Falconer

noncomputable def projectionGapConstant (κ : ℝ) : ℝ :=
  1+2*(1+2/(1-(2:ℝ)^(-κ)))

theorem projectionGapConstant_pos {κ : ℝ} (hκ : 0 < κ) :
    0 < projectionGapConstant κ := by
  have hd : 0 < 1-(2:ℝ)^(-κ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hκ]))
  unfold projectionGapConstant
  positivity

theorem planarPotentialConstant_gap {κ s t : ℝ} (hκ : 0 < κ)
    (hs : s ≤ 1) (hgap : κ ≤ t-s) :
    planarPotentialConstant s t ≤ projectionGapConstant κ := by
  have hp : (2:ℝ)^s ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hs
  have hq : (2:ℝ)^(s-t) ≤ (2:ℝ)^(-κ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hgap])
  have hd : 0 < 1-(2:ℝ)^(-κ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hκ]))
  have hden : 1-(2:ℝ)^(-κ) ≤ 1-(2:ℝ)^(s-t) := by linarith only [hq]
  have hquot : (2:ℝ)^s/(1-(2:ℝ)^(s-t)) ≤ 2/(1-(2:ℝ)^(-κ)) :=
    (div_le_div_of_nonneg_right hp (hd.le.trans hden)).trans
      (div_le_div_of_nonneg_left (by norm_num) hd hden)
  have hden0 : 0 < 1-(2:ℝ)^(s-t) := hd.trans_le hden
  have hq0 : 0 ≤ (2:ℝ)^s/(1-(2:ℝ)^(s-t)) := by positivity
  unfold planarPotentialConstant projectionGapConstant
  gcongr

 theorem projectionEnergyBudget_upper (N : ℕ) {s t KI KP D H : ℝ}
    (hst : s < t) (hs : s ≤ 1) (hKI : 0 ≤ KI) (hKP : 0 ≤ KP) (hD : 1 ≤ D)
    (hKIup : KI ≤ D) (hKPup : KP ≤ D)
    (hpotential : planarPotentialConstant s t ≤ H) :
    projectionEnergyBudget N s t KI KP ≤ (1+32*H)*((N:ℝ)+1)*D^2 := by
  have h2 : (2:ℝ)^s ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hs
  have h8 : (8:ℝ)^s ≤ 8 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 8) hs
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have hpotential0 : 0 < planarPotentialConstant s t := planarPotentialConstant_pos hst
  have hpoly : 1 ≤ ((N:ℝ)+1)*D^2 := by
    have hh : 1 ≤ D^2 := one_le_pow₀ hD
    nlinarith only [hN,hh]
  have hlarge : 1+(N:ℝ)*(2:ℝ)^s ≤ 2*((N:ℝ)+1) := by
    have hh := mul_le_mul_of_nonneg_left h2 hN
    linarith only [hh]
  unfold projectionEnergyBudget
  calc
    _ ≤ 1+(2*(2*((N:ℝ)+1))*D*8)*D*H := by gcongr
    _ = 1+32*H*((N:ℝ)+1)*D^2 := by ring
    _ ≤ _ := by nlinarith only [hpoly]

theorem projection_sample_log_budget (N : ℕ) :
    1-10*Real.log ((1/(2:ℝ)^N)/4) ≤ 100*((N:ℝ)+1) := by
  have he : (1/(2:ℝ)^N)/4 = 1/(2:ℝ)^(N+2) := by
    rw [pow_add]
    norm_num
    ring
  rw [he,Real.log_div one_ne_zero (by positivity),Real.log_one,Real.log_pow]
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  push_cast
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  nlinarith only [hlog,hN,mul_le_mul_of_nonneg_left hlog (show 0 ≤ (N:ℝ)+2 by positivity)]

theorem projectedSubsetSampleConstant_upper (N : ℕ) {s t KI KP ρ D H : ℝ}
    (hst : s < t) (hs : s ≤ 1) (hKI : 0 ≤ KI) (hKP : 0 ≤ KP)
    (hD : 1 ≤ D) (hKIup : KI ≤ D) (hKPup : KP ≤ D)
    (hρ : 0 < ρ) (hρlow : 1/D ≤ ρ) (hH : 0 ≤ H)
    (hpotential : planarPotentialConstant s t ≤ H) :
    projectedSubsetSampleConstant N s t KI KP ρ ≤
      (512*(64*Real.exp 1*(1+32*H)+100)^2)*((N:ℝ)+1)^2*D^8 := by
  let E := projectionEnergyBudget N s t KI KP
  let A := 1+32*H
  let C := (2*(2*E)/ρ)*(2/ρ)*(2:ℝ)^s
  let B := 1-10*Real.log ((1/(2:ℝ)^N)/4)
  have hE : 0 < E := projectionEnergyBudget_pos N hst hKI hKP
  have hA : 0 < A := by dsimp [A]; positivity
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have hD4 : 1 ≤ D^4 := one_le_pow₀ hD
  have hinv : 1/ρ ≤ D := by
    apply (div_le_iff₀ hρ).2
    have hh := (div_le_iff₀ hD0).1 hρlow
    linarith only [hh]
  have h2 : (2:ℝ)^s ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hs
  have h4 : (4:ℝ)^s ≤ 4 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) hs
  have h8 : (8:ℝ)^s ≤ 8 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 8) hs
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hC : C ≤ 16*A*((N:ℝ)+1)*D^4 := by
    have hfirst : 2*(2*E)/ρ ≤ 4*E*D := by
      calc
        _ = 4*E*(1/ρ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)
    have hsecond : 2/ρ ≤ 2*D := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0:ℝ) ≤ 2)
    calc
      C ≤ (4*E*D)*(2*D)*2 := by dsimp [C]; gcongr
      _ = 16*E*D^2 := by ring
      _ ≤ 16*(A*((N:ℝ)+1)*D^2)*D^2 := by
        gcongr
        exact projectionEnergyBudget_upper N hst hs hKI hKP hD hKIup hKPup hpotential
      _ = _ := by ring
  have hB : B ≤ 100*((N:ℝ)+1)*D^4 := by
    have hh := mul_le_mul_of_nonneg_left hD4
      (show 0 ≤ 100*((N:ℝ)+1) by positivity)
    exact (projection_sample_log_budget N).trans
      (by simpa only [mul_one] using hh)
  have hγ : 0 < (1/(2:ℝ)^N)/4 := by positivity
  have hγ1 : (1/(2:ℝ)^N)/4 ≤ 1 := by
    have hh : 1/(2:ℝ)^N ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
    linarith only [hh]
  have hB0 : 0 ≤ B := by
    have hh := Real.log_nonpos hγ.le hγ1
    dsimp [B]
    linarith only [hh]
  have hexp : 0 ≤ Real.exp 1-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
  have hT : ((Real.exp 1-1)*(C*(4:ℝ)^s)+B)*(8:ℝ)^s ≤
      8*(64*Real.exp 1*A+100)*((N:ℝ)+1)*D^4 := by
    calc
      _ ≤ (Real.exp 1*((16*A*((N:ℝ)+1)*D^4)*4)+100*((N:ℝ)+1)*D^4)*8 := by
        gcongr
        linarith only
      _ = _ := by ring
  have hT0 : 0 ≤ ((Real.exp 1-1)*(C*(4:ℝ)^s)+B)*(8:ℝ)^s := by positivity
  change 2*(2*(((Real.exp 1-1)*(C*(4:ℝ)^s)+B)*(8:ℝ)^s))^2 ≤ _
  calc
    _ ≤ 2*(2*(8*(64*Real.exp 1*A+100)*((N:ℝ)+1)*D^4))^2 := by gcongr
    _ = _ := by dsimp [A]; ring

end Falconer

end OAI
