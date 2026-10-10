import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileMatrixMajorant

namespace OAI

/-! The entrywise two-parameter Taylor step underlying the K=34 certificate. -/

open Matrix
namespace DefocusingNLS.ProfileCertificate

abbrev CMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev RealMatrix := Matrix (Fin 2) (Fin 2) ℝ

noncomputable def linearModel (U X Y : CMatrix) (b z : ℝ) : CMatrix := U+b • X+z • Y

theorem linearModel_step_identity (F G H U X Y A : CMatrix) (b z r : ℝ) :
    r • ((F+b • G+z • H)*A) -
        linearModel (r • (F*U)) (r • (G*U+F*X)) (r • (H*U+F*Y)) b z =
      r • ((F+(b • G+z • H))*(A-linearModel U X Y b z) +
        (b • G+z • H)*(b • X+z • Y)) := by
  simp only [linearModel, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, smul_smul]
  module

/-- The real matrix E is exactly the manuscript's second-order majorant. -/
theorem taylor_step_dominates (F G H U X Y A : CMatrix)
    (Fbound Gbound Hbound Xbound Ybound E : RealMatrix)
    (b z δ r : ℝ) (hr : 0 ≤ r) (hb : |b| ≤ δ) (hz : |z| ≤ δ)
    (hF : Dominates Fbound F) (hG : Dominates Gbound G)
    (hH : Dominates Hbound H) (hX : Dominates Xbound X) (hY : Dominates Ybound Y)
    (hE : Dominates (δ^2 • E) (A-linearModel U X Y b z)) :
    Dominates
      (δ^2 • (r • ((Fbound+δ • (Gbound+Hbound))*E +
        (Gbound+Hbound)*(Xbound+Ybound))))
      (r • ((F+b • G+z • H)*A) -
        linearModel (r • (F*U)) (r • (G*U+F*X)) (r • (H*U+F*Y)) b z) := by
  rw [linearModel_step_identity]
  have hP : Dominates (δ • (Gbound+Hbound)) (b • G+z • H) := by
    simpa only [smul_add] using (hG.smul_le b δ hb).add (hH.smul_le z δ hz)
  have hV : Dominates (δ • (Xbound+Ybound)) (b • X+z • Y) := by
    simpa only [smul_add] using (hX.smul_le b δ hb).add (hY.smul_le z δ hz)
  have h := ((hF.add hP).mul hE).add (hP.mul hV)
  have hs := h.smul r
  rw [abs_of_nonneg hr] at hs
  convert! hs using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, smul_eq_mul]
  ring

end DefocusingNLS.ProfileCertificate

end OAI
