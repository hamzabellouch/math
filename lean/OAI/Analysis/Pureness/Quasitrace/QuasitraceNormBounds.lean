import OAI.Analysis.Pureness.Quasitrace.QuasitraceContinuity

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace
open scoped NNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : PositiveQuasitrace D)

def twoSize (x : D) : ℝ := Real.sqrt (T (Positive.starMul x))

lemma twoSize_nonneg (x : D) : 0 ≤ T.twoSize x := Real.sqrt_nonneg _
lemma twoSize_sq (x : D) : T.twoSize x ^ 2 = T (Positive.starMul x) :=
  Real.sq_sqrt (T.nonneg _)
lemma twoSize_star (x : D) : T.twoSize (star x) = T.twoSize x := by
  unfold twoSize
  have h : Positive.starMul (star x) = Positive.mulStar x := Subtype.ext (by simp [Positive.starMul,Positive.mulStar])
  rw [h,← T.polar]

lemma squareValue_mul_le_left (x y : D) :
    T (Positive.starMul (x*y)) ≤ ‖x‖^2*T (Positive.starMul y) := by
  have h : Positive.starMul (x*y) ≤ Positive.smul (‖x‖₊^2) (Positive.starMul y) := by
    change star (x*y)*(x*y) ≤ (‖x‖₊^2 : ℝ≥0) • (star y*y)
    simp only [NNReal.smul_def,NNReal.coe_pow,coe_nnnorm,star_mul]
    rw [← mul_assoc,mul_assoc (star y) (star x),sq,← CStarRing.norm_star_mul_self (x := x)]
    exact CStarAlgebra.star_left_conjugate_le_norm_smul y (star x * x)
  have ht := T.monotone h
  rw [T.map_smul] at ht
  exact ht

lemma twoSize_mul_le_left (x y : D) : T.twoSize (x*y) ≤ ‖x‖*T.twoSize y := by
  rw [← sq_le_sq₀ (T.twoSize_nonneg _) (mul_nonneg (norm_nonneg _) (T.twoSize_nonneg _)),
    mul_pow,T.twoSize_sq,T.twoSize_sq]
  exact T.squareValue_mul_le_left x y

lemma twoSize_mul_le_right (x y : D) : T.twoSize (x*y) ≤ T.twoSize x*‖y‖ := by
  have h := T.twoSize_mul_le_left (star y) (star x)
  rw [← star_mul,T.twoSize_star,T.twoSize_star,norm_star] at h
  simpa only [mul_comm] using h
end CuntzPureness.PositiveQuasitrace

end

end OAI
