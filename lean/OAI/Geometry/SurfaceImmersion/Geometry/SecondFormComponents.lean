import OAI.Geometry.SurfaceImmersion.Geometry.ActualSecondFormFrame
import OAI.Geometry.SurfaceImmersion.Primitive.CrossingProjectionBounds
import OAI.Geometry.Immersion.ClosedSurface.ChartModel

namespace OAI

/-! Apply the scalar normal-component calculations to the actual second
fundamental form and its Euclidean unit frame. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes

lemma spaceCoordinates_symm_inner (v w : RVec 4) :
    inner ℝ (spaceCoordinates.symm v) (spaceCoordinates.symm w) = v ⬝ᵥ w := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (spaceCoordinates_dot (spaceCoordinates.symm v) (spaceCoordinates.symm w)).symm

lemma spaceCoordinates_norm_unit {v : RVec 4} (hv : v ⬝ᵥ v = 1) :
    ‖spaceCoordinates.symm v‖ = 1 := by
  have h := spaceCoordinates_symm_inner v v
  rw [real_inner_self_eq_norm_sq,hv] at h
  nlinarith [norm_nonneg (spaceCoordinates.symm v)]

namespace SecondFormFrame
variable {F : RField 4} {p : Base} {k : ℝ} (d : SecondFormFrame F p k)

lemma pure_components (hF : ContDiff ℝ ∞ F) (b c : ℝ) :
    realSecondForm F (b,c) (b,c) p =
      (pureComponents d.S d.D d.N d.L k b c).1 • d.n+
        (pureComponents d.S d.D d.N d.L k b c).2 • d.m := by
  rw [realSecondForm_bilinear hF]
  simp only [realSecondTensor,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    d.xx,d.xy,d.yy]
  ext j
  simp only [pureComponents,frameXX,frameXY,frameYY,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

lemma pure_space_components (hF : ContDiff ℝ ∞ F) (b c : ℝ) :
    spaceCoordinates.symm (realSecondForm F (b,c) (b,c) p) =
      frameVector (spaceCoordinates.symm d.n) (spaceCoordinates.symm d.m)
        (pureComponents d.S d.D d.N d.L k b c) := by
  rw [d.pure_components hF]
  simp only [map_add,map_smul,frameVector]

lemma slope_space_components (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    spaceCoordinates.symm (realSecondForm F (1,t) (1,t) p) =
      frameVector (spaceCoordinates.symm d.n) (spaceCoordinates.symm d.m)
        (slopePure d.S d.D d.N d.L k t) := by
  rw [d.pure_space_components hF,pure_unit_slope d.size_pos.ne']

lemma mixed_space_components (hF : ContDiff ℝ ∞ F) (t u : ℝ) :
    spaceCoordinates.symm (realSecondForm F (1,t) (1,u) p) =
      frameVector (spaceCoordinates.symm d.n) (spaceCoordinates.symm d.m)
        (slopeMixed d.S d.D d.N d.L k t u) := by
  have hvec : realSecondForm F (1,t) (1,u) p =
      (slopeMixed d.S d.D d.N d.L k t u).1 • d.n+
        (slopeMixed d.S d.D d.N d.L k t u).2 • d.m := by
    rw [realSecondForm_bilinear hF]
    simp only [realSecondTensor,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      d.xx,d.xy,d.yy]
    ext j
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,slopeMixed]
    field_simp [d.size_pos.ne']
    ring
  rw [hvec]
  simp only [map_add,map_smul,frameVector]

end SecondFormFrame
end ClosedSurfaceR4.GeometryPreservation

end

end OAI
