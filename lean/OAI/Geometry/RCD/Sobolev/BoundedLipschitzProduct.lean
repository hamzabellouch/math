import OAI.Geometry.RCD.Sobolev.InnerBallCutoffSequence

namespace OAI

/-! # Product tests needed for restriction of the measured approximation -/

open Set Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem bounded_unit_lipschitz_product {f g : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith 1 g)
    (hfb : ∀ x, |f x|≤1) (hgb : ∀ x, |g x|≤1) :
    LipschitzWith (L+1) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have he : f x*g x-f y*g y=f x*(g x-g y)+(f x-f y)*g y := by ring
  rw [he]
  calc
    _ ≤ |f x*(g x-g y)|+|(f x-f y)*g y| := abs_add_le _ _
    _ = |f x| * |g x-g y|+|f x-f y| * |g y| := by rw [abs_mul,abs_mul]
    _ ≤ |g x-g y|+|f x-f y| := by
      exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) (hfb x))
        (mul_le_of_le_one_right (abs_nonneg _) (hgb y))
    _ ≤ 1*dist x y+(L:ℝ)*dist x y := add_le_add (by simpa only [Real.dist_eq,NNReal.coe_one] using hg.dist_le_mul x y)
      (by simpa only [Real.dist_eq] using hf.dist_le_mul x y)
    _ = (L+1:ℝ≥0)*dist x y := by simp only [NNReal.coe_add,NNReal.coe_one]; ring

theorem bounded_lipschitz_product {f g : X → ℝ} {L M A B : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith M g)
    (hA : ∀ x, |f x| ≤ A) (hB : ∀ x, |g x| ≤ B) :
    LipschitzWith (A*M+B*L) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  calc
    _ = |f x*(g x-g y)+(f x-f y)*g y| := by congr 1; ring
    _ ≤ |f x| * |g x-g y|+|f x-f y| * |g y| := by
      simpa only [abs_mul] using abs_add_le (f x*(g x-g y)) ((f x-f y)*g y)
    _ ≤ (A:ℝ)*((M:ℝ)*dist x y)+((L:ℝ)*dist x y)*(B:ℝ) :=
      add_le_add
        (mul_le_mul (hA x) (by simpa only [Real.dist_eq] using hg.dist_le_mul x y)
          (abs_nonneg _) A.coe_nonneg)
        (mul_le_mul (by simpa only [Real.dist_eq] using hf.dist_le_mul x y) (hB y)
          (abs_nonneg _) (by positivity))
    _ = _ := by simp only [NNReal.coe_add,NNReal.coe_mul]; ring

end RegularPointCoordinates

end

end OAI
