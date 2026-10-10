import OAI.Geometry.SurfaceImmersion.Primitive.VelocityCoordinateData
import OAI.Geometry.Immersion.ClosedSurface.SecondForms

namespace OAI

/-! The manuscript's ordered crossing expression in coordinates adapted to
the boundary curve, for the actual second fundamental form. -/
noncomputable section
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes SmallModes

def orderedCrossing (F : RField 4) (v w p : Base) (κ : ℝ) : ℝ :=
  (realSecondForm F v w p ⬝ᵥ normalize (realSecondForm F v v p)) ^ 2 +
    κ * gramDet (coordDeriv v F p) (coordDeriv w F p)

theorem orderedCrossing_dy {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : realSecondForm F dy dy p ≠ 0) (b c κ : ℝ) :
    orderedCrossing F dy (b, c) p κ =
      (b * (coordDeriv dy (coordDeriv dx F) p ⬝ᵥ normalize (realSecondForm F dy dy p)) +
        c * Real.sqrt (realSecondForm F dy dy p ⬝ᵥ realSecondForm F dy dy p)) ^ 2 +
      (κ * gramDet (coordDeriv dx F p) (coordDeriv dy F p)) * b ^ 2 := by
  let B := realSecondForm F dy dy p
  let n := normalize B
  have hp := realNormalPart_perp (coordDeriv dx F p) (coordDeriv dy F p)
    (coordDeriv dy (coordDeriv dy F) p) hD
  have hXn : n ⬝ᵥ coordDeriv dx F p = 0 :=
    (dotProduct_comm _ _).trans (dot_normalize_zero hp.1)
  have hYn : n ⬝ᵥ coordDeriv dy F p = 0 :=
    (dotProduct_comm _ _).trans (dot_normalize_zero hp.2)
  have hm : realSecondForm F dx dy p ⬝ᵥ n = coordDeriv dy (coordDeriv dx F) p ⬝ᵥ n := by
    rw [realSecondForm, dotProduct_comm, dot_normalPart_eq hXn hYn, dotProduct_comm,
      real_second_coordDeriv_comm hF p dx dy]
  have hs : B ⬝ᵥ n = Real.sqrt (B ⬝ᵥ B) := dot_normalize_self hB
  have hBvw : realSecondForm F dy (b, c) p = b • realSecondForm F dx dy p + c • B := by
    rw [realSecondForm_bilinear hF]
    simp [dy, realSecondTensor, B]
  have hW : coordDeriv (b, c) F p = b • coordDeriv dx F p + c • coordDeriv dy F p :=
    coordDeriv_eq_basis F (b, c) p
  have hg : gramDet (coordDeriv dy F p) (coordDeriv (b, c) F p) =
      b ^ 2 * gramDet (coordDeriv dx F p) (coordDeriv dy F p) := by
    rw [hW]
    convert gramDet_change_basis (coordDeriv dx F p) (coordDeriv dy F p) 0 1 b c using 1 <;>
      simp
  change (realSecondForm F dy (b, c) p ⬝ᵥ n) ^ 2 + _ = _
  rw [hBvw, add_dotProduct, smul_dotProduct, smul_dotProduct, hm, hs, hg]
  change (b * _ + c * _) ^ 2 + _ = _
  ring

end ClosedSurfaceR4.VelocityFrame

end

end OAI
