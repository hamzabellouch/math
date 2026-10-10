import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileCertificateRecipe
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! The exact inner boundary radius fixed in the manuscript. -/

namespace DefocusingNLS

noncomputable def innerBoundaryRadius : ℝ :=
  2*Real.sqrt (ProfileCertificate.centerZ : ℝ)+1/10000

theorem innerBoundaryRadius_bounds : 1 ≤ innerBoundaryRadius ∧ innerBoundaryRadius^2 ≤ 11 := by
  have hz : (27/10 : ℝ) ≤ (ProfileCertificate.centerZ : ℝ) ∧
      (ProfileCertificate.centerZ : ℝ) ≤ (271/100 : ℝ) := by
    norm_num [ProfileCertificate.centerZ]
  have hz0 : 0 ≤ (ProfileCertificate.centerZ : ℝ) := le_trans (by norm_num) hz.1
  have hs := Real.sq_sqrt hz0
  have hsn := Real.sqrt_nonneg (ProfileCertificate.centerZ : ℝ)
  have hsl : (3/2 : ℝ) ≤ Real.sqrt (ProfileCertificate.centerZ : ℝ) := by nlinarith [hz.1]
  have hsu : Real.sqrt (ProfileCertificate.centerZ : ℝ) ≤ (33/20 : ℝ) := by nlinarith [hz.2]
  unfold innerBoundaryRadius
  constructor <;> nlinarith

end DefocusingNLS

end OAI
