import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPaperRadius
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace OAI

/-! All certified parameter radii lie in the short shell used by the boundary-modulus estimate. -/

open Set
namespace DefocusingNLS

theorem radial_boundary_shell_geometry (Z : ℝ)
    (hZ : |Z-(ProfileCertificate.centerZ : ℝ)| ≤ (1/100000000 : ℝ)) :
    (3 : ℝ) ≤ 2*Real.sqrt Z ∧ innerBoundaryRadius ≤ (10/3 : ℝ) ∧
      innerBoundaryRadius-2*Real.sqrt Z ∈
        Icc (1/10000-1/100000000 : ℝ) (1/10000+1/100000000) := by
  have hz := abs_le.mp hZ
  have hc : (27/10 : ℝ) ≤ (ProfileCertificate.centerZ : ℝ) ∧
      (ProfileCertificate.centerZ : ℝ) ≤ (271/100 : ℝ) := by norm_num [ProfileCertificate.centerZ]
  have hZ0 : 0 ≤ Z := by linarith [hz.1,hc.1]
  have hC0 : 0 ≤ (ProfileCertificate.centerZ : ℝ) := by linarith [hc.1]
  have hsq := Real.sq_sqrt hZ0
  have hcq := Real.sq_sqrt hC0
  have hn := Real.sqrt_nonneg Z
  have hcn := Real.sqrt_nonneg (ProfileCertificate.centerZ : ℝ)
  have hZl : (3/2 : ℝ) ≤ Real.sqrt Z := by nlinarith [hz.1,hc.1]
  have hCl : (3/2 : ℝ) ≤ Real.sqrt (ProfileCertificate.centerZ : ℝ) := by nlinarith [hc.1]
  have hCu : Real.sqrt (ProfileCertificate.centerZ : ℝ) ≤ (33/20 : ℝ) := by nlinarith [hc.2]
  have hid : (Real.sqrt Z-Real.sqrt (ProfileCertificate.centerZ : ℝ))*
      (Real.sqrt Z+Real.sqrt (ProfileCertificate.centerZ : ℝ))=Z-(ProfileCertificate.centerZ : ℝ) := by
    nlinarith
  have hab : |Real.sqrt Z-Real.sqrt (ProfileCertificate.centerZ : ℝ)| *
      (Real.sqrt Z+Real.sqrt (ProfileCertificate.centerZ : ℝ)) ≤ (1/100000000 : ℝ) := by
    rw [← abs_of_nonneg (add_nonneg hn hcn),← abs_mul,hid]
    exact hZ
  have hs : |Real.sqrt Z-Real.sqrt (ProfileCertificate.centerZ : ℝ)| ≤ (1/300000000 : ℝ) := by
    nlinarith [abs_nonneg (Real.sqrt Z-Real.sqrt (ProfileCertificate.centerZ : ℝ))]
  have hsd := abs_le.mp hs
  unfold innerBoundaryRadius
  constructor
  · linarith
  constructor
  · linarith
  · constructor <;> linarith [hsd.1,hsd.2]

end DefocusingNLS

end OAI
