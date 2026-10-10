import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryProfileGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.VelocityNormalGeometry

namespace OAI

/-! The preferred and complementary normals of a regular five-profile. -/
noncomputable section
open scoped Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame RealModes VelocityFrame

lemma profilePreferred_unit {J : BoundaryProfile} (hJ : J ∈ regularBoundaryProfiles) :
    profilePreferred J ⬝ᵥ profilePreferred J = 1 := normalize_unit hJ.2

lemma profilePreferred_perp {J : BoundaryProfile} (hJ : J ∈ regularBoundaryProfiles) :
    J 0 ⬝ᵥ profilePreferred J = 0 ∧ J 1 ⬝ᵥ profilePreferred J = 0 := by
  have hh := realNormalPart_perp (J 0) (J 1) (J 2) hJ.1
  exact ⟨dot_normalize_zero hh.1,dot_normalize_zero hh.2⟩

lemma profileComplement_unit {J : BoundaryProfile} (hJ : J ∈ regularBoundaryProfiles) :
    profileComplement J ⬝ᵥ profileComplement J = 1 :=
  unitPerp_unit hJ.1 (normalize_nonzero hJ.2)
    (profilePreferred_perp hJ).1 (profilePreferred_perp hJ).2

lemma profileComplement_perp (J : BoundaryProfile) :
    J 0 ⬝ᵥ profileComplement J = 0 ∧ J 1 ⬝ᵥ profileComplement J = 0 ∧
      profilePreferred J ⬝ᵥ profileComplement J = 0 := unitPerp_orthogonal _ _ _

/-- Every unit normal orthogonal to the preferred normal reads the same
absolute complementary coefficient, regardless of the orientation choice. -/
lemma profileComplement_abs_dot {J : BoundaryProfile} (hJ : J ∈ regularBoundaryProfiles)
    {u : Vec} (hu : u ⬝ᵥ u = 1) (hXu : J 0 ⬝ᵥ u = 0) (hYu : J 1 ⬝ᵥ u = 0)
    (hnu : profilePreferred J ⬝ᵥ u = 0) (W : Vec) :
    |W ⬝ᵥ profileComplement J| = |W ⬝ᵥ u| := by
  have hp := profilePreferred_perp hJ
  have hm := profileComplement_perp J
  have hr := plane_coordinates_reconstruct hJ.1 (profilePreferred_unit hJ)
    (profileComplement_unit hJ) hm.2.2 hp.1 hm.1 hp.2 hm.2.1 hXu hYu
  have he : (u ⬝ᵥ profileComplement J) • profileComplement J = u := by
    simpa only [planeLift_apply,planeCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one,
      dotProduct_comm u (profilePreferred J),hnu,zero_smul,zero_add] using hr
  have hl := plane_coordinates_length hJ.1 (profilePreferred_unit hJ)
    (profileComplement_unit hJ) hm.2.2 hp.1 hm.1 hp.2 hm.2.1 hXu hYu
  have hs : (u ⬝ᵥ profileComplement J)^2 = 1 := by
    simpa only [dotProduct_comm u (profilePreferred J),hnu,zero_pow (by decide : 2 ≠ 0),
      zero_add,hu] using hl
  have ha : |u ⬝ᵥ profileComplement J| = 1 := by
    nlinarith [sq_abs (u ⬝ᵥ profileComplement J),abs_nonneg (u ⬝ᵥ profileComplement J)]
  calc
    |W ⬝ᵥ profileComplement J| = |u ⬝ᵥ profileComplement J| * |W ⬝ᵥ profileComplement J| := by rw [ha,one_mul]
    _ = |W ⬝ᵥ ((u ⬝ᵥ profileComplement J) • profileComplement J)| := by
      rw [dotProduct_smul,smul_eq_mul,abs_mul]
    _ = |W ⬝ᵥ u| := by rw [he]

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
