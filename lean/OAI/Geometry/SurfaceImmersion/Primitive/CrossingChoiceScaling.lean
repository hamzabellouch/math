import OAI.Geometry.SurfaceImmersion.Primitive.ProfileCrossingChoice

namespace OAI

/-! Crossing normal choices are invariant under the positive squares arising
when a nonvertical curve direction is written in slope coordinates. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma crossing_choice_scale {n p q : Vec} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hchoice : (0 < p ⬝ᵥ n ∧ 0 < q ⬝ᵥ n) ∨
      (0 < p ⬝ᵥ q ∧ ∃ w : Vec, n ⬝ᵥ w = 0 ∧ 0 < p ⬝ᵥ w ∧ 0 < q ⬝ᵥ w)) :
    (0 < (r • p) ⬝ᵥ n ∧ 0 < (s • q) ⬝ᵥ n) ∨
      (0 < (r • p) ⬝ᵥ (s • q) ∧ ∃ w : Vec, n ⬝ᵥ w = 0 ∧
        0 < (r • p) ⬝ᵥ w ∧ 0 < (s • q) ⬝ᵥ w) := by
  rcases hchoice with ⟨hp,hq⟩ | ⟨hpq,w,hnw,hpw,hqw⟩
  · left
    simpa only [smul_dotProduct,smul_eq_mul] using And.intro (mul_pos hr hp) (mul_pos hs hq)
  · right
    refine ⟨?_,w,hnw,?_,?_⟩
    · simpa only [smul_dotProduct,dotProduct_smul,smul_eq_mul,mul_assoc] using mul_pos hs (mul_pos hr hpq)
    · simpa only [smul_dotProduct,smul_eq_mul] using mul_pos hr hpw
    · simpa only [smul_dotProduct,smul_eq_mul] using mul_pos hs hqw

lemma realSecondForm_smul_self {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (r : ℝ) (v p : Base) :
    realSecondForm F (r • v) (r • v) p = r^2 • realSecondForm F v v p := by
  rw [realSecondForm_quadratic hF,PhaseGeometry.secondQuadratic_smul,
    ← realSecondForm_quadratic hF]

lemma realSecondForm_firstSlope {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (b c : ℝ) (p : Base) (hb : b ≠ 0) :
    realSecondForm F (b,c) (b,c) p = b^2 • realSecondForm F (1,c/b) (1,c/b) p := by
  have hv : (b,c) = b • ((1,c/b) : Base) := by
    apply Prod.ext
    · simp
    · change c = b*(c/b)
      field_simp
  rw [hv,realSecondForm_smul_self hF]

lemma crossing_choice_firstSlope {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p : Base) (n : Vec) (v w : Base) (hv : v.1 ≠ 0) (hw : w.1 ≠ 0)
    (hchoice :
      (0 < realSecondForm F (1,v.2/v.1) (1,v.2/v.1) p ⬝ᵥ n ∧
       0 < realSecondForm F (1,w.2/w.1) (1,w.2/w.1) p ⬝ᵥ n) ∨
      (0 < realSecondForm F (1,v.2/v.1) (1,v.2/v.1) p ⬝ᵥ
        realSecondForm F (1,w.2/w.1) (1,w.2/w.1) p ∧
       ∃ a : Vec, n ⬝ᵥ a = 0 ∧
        0 < realSecondForm F (1,v.2/v.1) (1,v.2/v.1) p ⬝ᵥ a ∧
        0 < realSecondForm F (1,w.2/w.1) (1,w.2/w.1) p ⬝ᵥ a)) :
    (0 < realSecondForm F v v p ⬝ᵥ n ∧ 0 < realSecondForm F w w p ⬝ᵥ n) ∨
      (0 < realSecondForm F v v p ⬝ᵥ realSecondForm F w w p ∧
       ∃ a : Vec, n ⬝ᵥ a = 0 ∧
        0 < realSecondForm F v v p ⬝ᵥ a ∧ 0 < realSecondForm F w w p ⬝ᵥ a) := by
  have h := crossing_choice_scale (sq_pos_of_ne_zero hv) (sq_pos_of_ne_zero hw) hchoice
  rw [← realSecondForm_firstSlope hF v.1 v.2 p hv,
    ← realSecondForm_firstSlope hF w.1 w.2 p hw] at h
  exact h

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
