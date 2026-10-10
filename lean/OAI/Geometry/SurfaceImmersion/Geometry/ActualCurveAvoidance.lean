import OAI.Geometry.SurfaceImmersion.Primitive.ActualCrossingInvariant
import OAI.Geometry.SurfaceImmersion.Geometry.CompactCurveAvoidance

namespace OAI

/-! Turn the componentwise ray exclusion into nonvanishing and non-antipodality
for the actual unit normal and second fundamental form. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes VelocityFrame

lemma frameVector_avoids_negative_axis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n m : E} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hmn : inner ℝ m n = 0)
    {v : ℝ × ℝ} (hv : 0 < v.1 ∨ v.2 ≠ 0) :
    frameVector n m v ≠ 0 ∧ ‖frameVector n m v‖⁻¹ • frameVector n m v ≠ -n := by
  let P := frameVector n m v
  have hfirst : inner ℝ P n = v.1 := frameVector_inner_first hn hmn v
  have hsecond : inner ℝ P m = v.2 := frameVector_inner_second hm hmn v
  have hP : P ≠ 0 := by
    intro hz
    rw [hz,inner_zero_left] at hfirst hsecond
    rcases hv with hp | hs
    · linarith
    · exact hs hsecond.symm
  refine ⟨hP,?_⟩
  intro heq
  have hscale : ‖P‖ • (‖P‖⁻¹ • P) = P := by
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hP),one_smul]
  have hPeq : P = (-‖P‖) • n := by
    rw [heq] at hscale
    simpa only [smul_neg,neg_smul] using hscale.symm
  have hnm : inner ℝ n m = 0 := by rw [real_inner_comm]; exact hmn
  rw [hPeq,real_inner_smul_left,real_inner_self_eq_norm_sq,hn,one_pow,mul_one] at hfirst
  rw [hPeq,real_inner_smul_left,hnm,mul_zero] at hsecond
  rcases hv with hp | hs
  · linarith [norm_nonneg P]
  · exact hs hsecond.symm

namespace SecondFormFrame
variable {F : RField 4} {p : Base} {k : ℝ} (d : SecondFormFrame F p k)

lemma actual_curve_avoidance (hF : ContDiff ℝ ∞ F) (b c : ℝ)
    (hcomp : 0 < (pureComponents d.S d.D d.N d.L k b c).1 ∨
      (pureComponents d.S d.D d.N d.L k b c).2 ≠ 0) :
    realSecondForm F (b,c) (b,c) p ≠ 0 ∧
      normalize (realSecondForm F (b,c) (b,c) p) ≠ -d.n := by
  have hmn : inner ℝ (spaceCoordinates.symm d.m) (spaceCoordinates.symm d.n) = 0 := by
    rw [spaceCoordinates_symm_inner, dotProduct_comm]
    exact d.orthogonal
  obtain ⟨hneq,hanti⟩ := frameVector_avoids_negative_axis
    (spaceCoordinates_norm_unit d.unit_n) (spaceCoordinates_norm_unit d.unit_m) hmn hcomp
  rw [← d.pure_space_components hF b c] at hneq hanti
  constructor
  · intro hz
    rw [hz,map_zero] at hneq
    exact hneq rfl
  · intro heq
    apply hanti
    have he := congrArg spaceCoordinates.symm heq
    simpa only [spaceCoordinates_symm_normalize,map_neg] using he

end SecondFormFrame
end ClosedSurfaceR4.GeometryPreservation

end

end OAI
