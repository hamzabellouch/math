import OAI.Analysis.LipschitzHilbert.Trees.SourceReverseWeights
import OAI.Analysis.LipschitzHilbert.Trees.SourceModelThresholdScale

namespace OAI

/-! Normalize removal budgets while keeping the independent size cap. -/
noncomputable section
namespace LipschitzHilbert

theorem combine_capped_removal_budgets
    (A B Q cap sigma density eta area energy : ℝ)
    (hB : 0≤B) (hQ : 0≤Q) (hcap : 0≤cap) (hsigma : 0<sigma)
    (hdensity : 0≤density) (heta : 0<eta) (harea : 0≤area)
    (hscale : sigma^2*area=eta*energy) :
    A*cap*density*(1+eta^(-(1/20:ℝ)))*(2*area/eta)+
      B*cap*density*((Q/sigma^2)*energy) ≤
    (2*A+B*Q)*cap*density*(1+eta^(-(1/20:ℝ)))*area/eta := by
  have hratio : (Q/sigma^2)*energy=Q*area/eta := by
    field_simp
    nlinarith [congrArg (fun x : ℝ => Q*x) hscale]
  rw [hratio]
  have hfac : 1≤1+eta^(-(1/20:ℝ)) := le_add_of_nonneg_right (Real.rpow_nonneg heta.le _)
  have hb : 0≤B*cap*density*(Q*area/eta) := by positivity
  calc
    _ ≤ A*cap*density*(1+eta^(-(1/20:ℝ)))*(2*area/eta)+
        (B*cap*density*(Q*area/eta))*(1+eta^(-(1/20:ℝ))) :=
      add_le_add le_rfl (le_mul_of_one_le_right hb hfac)
    _ = _ := by ring

theorem min_scaled_le (a b x : ℝ) (hx : 0≤x) :
    min a (b*x)≤max a b*min 1 x := by
  by_cases h : x≤1
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx)
  · rw [min_eq_left (le_of_not_ge h),mul_one]
    exact (min_le_left _ _).trans (le_max_left _ _)

theorem capped_density_weight_le (cap density eta ratio K U : ℝ)
    (heta : 0<eta) (hK : 0≤K) (hdensity : 0≤density)
    (hcapBound : cap≤K*min 1 (Real.sqrt (eta/ratio)))
    (hdensityBound : density≤U*min 1 eta) :
    cap*density*(1+eta^(-(1/20:ℝ)))/eta≤K*U*reverseThresholdWeight ratio eta := by
  have hmult := mul_le_mul hcapBound hdensityBound hdensity
    (mul_nonneg hK (le_min zero_le_one (Real.sqrt_nonneg _)))
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmult (by positivity : 0≤1+eta^(-(1/20:ℝ)))) heta.le
  convert h using 1
  unfold reverseThresholdWeight
  ring

theorem modelSizeThreshold_eq_sqrt_ratio {energyNorm area : ℝ}
    (hN : 0<energyNorm) (hA : 0<area) (k : ℤ) :
    modelSizeThreshold energyNorm area k=Real.sqrt ((2:ℝ)^k/(area/energyNorm^2)) := by
  have hleft := modelSizeThreshold_pos hN hA k
  have heta := zpow_pos (by norm_num : (0:ℝ)<2) k
  have hid := modelSizeThreshold_identity energyNorm area hA k
  apply (sq_eq_sq₀ hleft.le (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity)]
  field_simp
  exact hid

end LipschitzHilbert

end

end OAI
