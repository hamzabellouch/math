import OAI.Analysis.LipschitzHilbert.Trees.SourceThresholdWeights

namespace OAI

/-! Normalize the two ordinary removal budgets at the common size
threshold sigma² = eta times energy / area. -/
noncomputable section
namespace LipschitzHilbert

theorem combine_ordinary_removal_budgets
    (A B Q D sigma density eta area energy : ℝ)
    (hB : 0≤B) (hQ : 0≤Q) (hD : 0≤D) (hsigma : 0<sigma)
    (hdensity : 0≤density) (heta : 0<eta) (harea : 0≤area)
    (hscale : sigma^2*area=eta*energy) :
    A*(D*sigma)*density*(1+eta^(-(1/20:ℝ)))*(2*area/eta)+
      B*(D*sigma)*density*((Q/sigma^2)*energy) ≤
    (D*(2*A+B*Q))*(sigma*area/Real.sqrt eta)*
      (density*Real.sqrt eta*(1+eta^(-(1/20:ℝ)))/eta) := by
  have hratio : (Q/sigma^2)*energy=Q*area/eta := by
    field_simp
    nlinarith [congrArg (fun x : ℝ => Q*x) hscale]
  rw [hratio]
  have hfac : 1≤1+eta^(-(1/20:ℝ)) :=
    le_add_of_nonneg_right (Real.rpow_nonneg heta.le _)
  have hb : 0≤B*(D*sigma)*density*(Q*area/eta) := by positivity
  have hsqrt : Real.sqrt eta≠0 := (Real.sqrt_pos.mpr heta).ne'
  calc
    _ ≤ A*(D*sigma)*density*(1+eta^(-(1/20:ℝ)))*(2*area/eta)+
        (B*(D*sigma)*density*(Q*area/eta))*(1+eta^(-(1/20:ℝ))) := by
      exact add_le_add le_rfl (le_mul_of_one_le_right hb hfac)
    _ = _ := by field_simp [hsqrt]

theorem normalized_size_area_factor (eta energyNorm area : ℝ)
    (heta : 0<eta) (harea : 0<area) :
    ((Real.sqrt eta*energyNorm/Real.sqrt area)*area/Real.sqrt eta)=
      energyNorm*Real.sqrt area := by
  have hse := (Real.sqrt_pos.mpr heta).ne'
  have hsa := (Real.sqrt_pos.mpr harea).ne'
  field_simp [hse,hsa]
  rw [Real.sq_sqrt harea.le]

theorem normalized_size_identity (eta energyNorm area : ℝ) (harea : 0<area) (heta : 0≤eta) :
    (Real.sqrt eta*energyNorm/Real.sqrt area)^2*area=eta*energyNorm^2 := by
  rw [div_pow,mul_pow,Real.sq_sqrt heta,Real.sq_sqrt harea.le]
  field_simp

end LipschitzHilbert

end

end OAI
