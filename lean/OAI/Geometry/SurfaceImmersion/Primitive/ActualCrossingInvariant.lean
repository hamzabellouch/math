import OAI.Geometry.SurfaceImmersion.Geometry.SecondFormComponents
import OAI.Geometry.SurfaceImmersion.Primitive.CrossingInvariantThreshold

namespace OAI

/-! Identify the actual ordered boundary invariant with the normal-coordinate
formula.  Euclidean normalization is preserved by the coordinate conversion. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes VelocityFrame

lemma spaceCoordinates_norm (v : RVec 4) :
    ‖spaceCoordinates.symm v‖ = Real.sqrt (v ⬝ᵥ v) := by
  rw [← spaceCoordinates_symm_inner,real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]

lemma spaceCoordinates_symm_normalize (v : RVec 4) :
    spaceCoordinates.symm (normalize v) = ‖spaceCoordinates.symm v‖⁻¹ • spaceCoordinates.symm v := by
  simp only [VelocityFrame.normalize,map_smul,spaceCoordinates_norm]

namespace SecondFormFrame
variable {F : RField 4} {p : Base} {k : ℝ} (d : SecondFormFrame F p k)

lemma orderedCrossing_eq (hF : ContDiff ℝ ∞ F) (κ t u : ℝ)
    (hk : k = κ*NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p)) :
    orderedCrossing F (1,t) (1,u) p κ =
      modelOrderedCrossing (spaceCoordinates.symm d.n) (spaceCoordinates.symm d.m)
        d.S d.D d.N d.L k t u := by
  have hg : NormalFrame.gramDet (coordDeriv (1,t) F p) (coordDeriv (1,u) F p) =
      (u-t)^2*NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) := by
    rw [coordDeriv_eq_basis F (1,t),coordDeriv_eq_basis F (1,u)]
    simpa only [one_mul,mul_one] using gramDet_change_basis (coordDeriv dx F p)
      (coordDeriv dy F p) 1 t 1 u
  unfold orderedCrossing
  rw [← spaceCoordinates_symm_inner,spaceCoordinates_symm_normalize,
    d.mixed_space_components hF,d.slope_space_components hF,hg]
  unfold modelOrderedCrossing
  congr 1
  rw [hk]
  ring

end SecondFormFrame
end ClosedSurfaceR4.GeometryPreservation

end

end OAI
