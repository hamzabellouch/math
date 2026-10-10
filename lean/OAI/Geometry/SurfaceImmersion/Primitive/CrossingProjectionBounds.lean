import OAI.Geometry.SurfaceImmersion.Primitive.CrossingComponents

namespace OAI

/-! The ordered mixed projection is bounded independently of the unbounded
longitudinal second-form component. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mixed_projection_lower {P Z : E} (hP : P ≠ 0) :
    ‖P‖-‖Z-P‖ ≤ inner ℝ Z (‖P‖⁻¹ • P) := by
  have hp : 0 < ‖P‖ := norm_pos_iff.mpr hP
  have hi : -‖Z-P‖*‖P‖ ≤ inner ℝ (Z-P) P := by
    have h := (neg_abs_le (inner ℝ (Z-P) P)).trans' (neg_le_neg (abs_real_inner_le_norm (Z-P) P))
    simpa only [neg_mul] using h
  have he : inner ℝ Z P = inner ℝ (Z-P) P+‖P‖^2 := by
    rw [inner_sub_left,real_inner_self_eq_norm_sq]
    ring
  rw [real_inner_smul_right,he]
  calc
    ‖P‖-‖Z-P‖ = (‖P‖^2-‖Z-P‖*‖P‖)/‖P‖ := by field_simp
    _ ≤ (inner ℝ (Z-P) P+‖P‖^2)/‖P‖ :=
      div_le_div_of_nonneg_right (by linarith) hp.le
    _ = ‖P‖⁻¹*(inner ℝ (Z-P) P+‖P‖^2) := by ring

def frameVector (n m : E) (v : ℝ × ℝ) : E := v.1 • n+v.2 • m

lemma frameVector_sub (n m : E) (v w : ℝ × ℝ) :
    frameVector n m (v-w) = frameVector n m v-frameVector n m w := by
  simp only [frameVector,Prod.fst_sub,Prod.snd_sub,sub_smul]
  abel

lemma frameVector_smul (n m : E) (a : ℝ) (v : ℝ × ℝ) :
    frameVector n m (a • v) = a • frameVector n m v := by
  simp only [frameVector,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,smul_add,smul_smul]

lemma frameVector_norm_le {n m : E} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (v : ℝ × ℝ) :
    ‖frameVector n m v‖ ≤ |v.1|+|v.2| := by
  simpa only [frameVector,norm_smul,Real.norm_eq_abs,hn,hm,mul_one] using
    norm_add_le (v.1 • n) (v.2 • m)

lemma frameVector_inner_first {n m : E} (hn : ‖n‖ = 1) (hmn : inner ℝ m n = 0)
    (v : ℝ × ℝ) : inner ℝ (frameVector n m v) n = v.1 := by
  simp only [frameVector,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
    hn,one_pow,hmn,mul_one,mul_zero,add_zero]

theorem crossing_projection_lower {n m : E} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    (hmn : inner ℝ m n = 0) {S D N L k t u : ℝ} (hS : S ≠ 0)
    (hp : 0 < (slopePure S D N L k t).1) :
    (slopePure S D N L k t).1-|u-t| *(|D+S*t|+|N|) ≤
      inner ℝ (frameVector n m (slopeMixed S D N L k t u))
        (‖frameVector n m (slopePure S D N L k t)‖⁻¹ •
          frameVector n m (slopePure S D N L k t)) := by
  let P := frameVector n m (slopePure S D N L k t)
  let Z := frameVector n m (slopeMixed S D N L k t u)
  have hip : inner ℝ P n = (slopePure S D N L k t).1 := frameVector_inner_first hn hmn _
  have hP : P ≠ 0 := by
    intro h
    rw [h,inner_zero_left] at hip
    linarith
  have hPn : (slopePure S D N L k t).1 ≤ ‖P‖ := by
    rw [← hip]
    simpa only [hn,mul_one] using real_inner_le_norm P n
  have he : Z-P = (u-t) • frameVector n m (D+S*t,N) := by
    change frameVector n m (slopeMixed S D N L k t u)-
      frameVector n m (slopePure S D N L k t) = _
    rw [← frameVector_sub,mixed_sub_left hS,frameVector_smul]
  have hdiff : ‖Z-P‖ ≤ |u-t| *(|D+S*t|+|N|) := by
    rw [he,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (frameVector_norm_le hn hm _) (abs_nonneg _)
  exact (sub_le_sub hPn hdiff).trans (mixed_projection_lower hP)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
