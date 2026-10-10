import OAI.Analysis.LipschitzHilbert.Trees.SourceStepArithmetic

namespace OAI

/-! The size threshold used at each dyadic density level. -/
noncomputable section
namespace LipschitzHilbert

def modelSizeThreshold (energyNorm area : ℝ) (k : ℤ) : ℝ :=
  Real.sqrt ((2:ℝ)^k)*energyNorm/Real.sqrt area

theorem modelSizeThreshold_pos {energyNorm area : ℝ}
    (hN : 0<energyNorm) (hA : 0<area) (k : ℤ) :
    0<modelSizeThreshold energyNorm area k := by
  unfold modelSizeThreshold
  positivity

theorem modelSizeThreshold_identity (energyNorm area : ℝ) (hA : 0<area) (k : ℤ) :
    (modelSizeThreshold energyNorm area k)^2*area=(2:ℝ)^k*energyNorm^2 :=
  normalized_size_identity _ _ _ hA (zpow_pos (by norm_num) k).le

theorem modelSizeThreshold_successive (energyNorm area : ℝ) (hA : 0<area) (k : ℤ) :
    (modelSizeThreshold energyNorm area k)^2=
      (Real.sqrt 2*modelSizeThreshold energyNorm area (k-1))^2 := by
  apply (mul_right_cancel₀ hA.ne')
  rw [modelSizeThreshold_identity energyNorm area hA k,mul_pow,Real.sq_sqrt (by norm_num),mul_assoc,
    modelSizeThreshold_identity energyNorm area hA (k-1)]
  rw [zpow_sub₀ (by norm_num),zpow_one]
  ring

theorem modelSizeThreshold_normalized (energyNorm area : ℝ) (hA : 0<area) (k : ℤ) :
    modelSizeThreshold energyNorm area k*area/Real.sqrt ((2:ℝ)^k)=energyNorm*Real.sqrt area :=
  normalized_size_area_factor _ _ _ (zpow_pos (by norm_num) k) hA

end LipschitzHilbert

end

end OAI
