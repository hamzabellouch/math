import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryProfileNormal
import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryProfileFrame

namespace OAI

/-! Smooth fields of actual second forms and their preferred unit normal. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma realSecondForm_smoothOn {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {U : Set Base}
    (hD : ∀ x ∈ U, gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0)
    (v w : Base) : ContDiffOn ℝ ∞ (realSecondForm F v w) U := by
  intro x hx
  exact (contDiffAt_realNormalPart
    (contDiff_real_coordDeriv hF dx).contDiffAt
    (contDiff_real_coordDeriv hF dy).contDiffAt
    (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF w) v).contDiffAt
    (hD x hx)).contDiffWithinAt

lemma realSecondForm_variable_smoothOn {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {U : Set Base}
    (hD : ∀ x ∈ U, gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0)
    {v : Base → Base} (hv : ContDiffOn ℝ ∞ v U) :
    ContDiffOn ℝ ∞ (fun x => realSecondForm F (v x) (v x) x) U := by
  have hx := realSecondForm_smoothOn hF hD dx dx
  have hxy := realSecondForm_smoothOn hF hD dx dy
  have hy := realSecondForm_smoothOn hF hD dy dy
  have hvx : ContDiffOn ℝ ∞ (fun x => (v x).1) U := contDiff_fst.comp_contDiffOn hv
  have hvy : ContDiffOn ℝ ∞ (fun x => (v x).2) U := contDiff_snd.comp_contDiffOn hv
  have hh := (((hvx.pow 2).smul hx).add
    ((((contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Base => (2:ℝ)) U).mul hvx).mul hvy).smul hxy)).add ((hvy.pow 2).smul hy)
  convert hh using 1
  funext x
  rw [realSecondForm_quadratic hF]
  rfl

lemma realBoundaryProfile_smooth {F : RField 4} (hF : ContDiff ℝ ∞ F) (z : ℝ) :
    ContDiff ℝ ∞ (realBoundaryProfile F z) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_real_coordDeriv hF dx
  · exact contDiff_real_coordDeriv hF dy
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dx
  · exact (contDiff_const : ContDiff ℝ ∞ (fun _ : Base => z)).smul (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dx) dx)

lemma profilePreferred_field_smoothOn {F : RField 4} (hF : ContDiff ℝ ∞ F) (z : ℝ)
    {U : Set Base} (hreg : ∀ x ∈ U, realBoundaryProfile F z x ∈ regularBoundaryProfiles) :
    ContDiffOn ℝ ∞ (fun x => profilePreferred (realBoundaryProfile F z x)) U := by
  intro x hx
  exact ((contDiffAt_profilePreferred (hreg x hx)).comp x
    (realBoundaryProfile_smooth hF z).contDiffAt).contDiffWithinAt

lemma realSecondForm_field_perp {F : RField 4} {x : Base}
    (hD : gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0) (v w : Base) :
    coordDeriv dx F x ⬝ᵥ realSecondForm F v w x = 0 ∧
    coordDeriv dy F x ⬝ᵥ realSecondForm F v w x = 0 :=
  realNormalPart_perp _ _ _ hD

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
