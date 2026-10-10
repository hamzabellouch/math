import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricQuasiEquivalence

namespace OAI

/-! # Uniform coarse inverse bounds for self quasi-isometries -/

noncomputable section
namespace PolycyclicRecognition

variable (G : Type*) [PseudoMetricSpace G] (K C : ℝ)

/-- The usual upper, lower and coarse-surjectivity inequalities, with the
lower inequality multiplied by `K` to avoid division. For `1 ≤ K` this is
exactly the standard `(K,C)` definition. -/
structure SelfQuasiIsometry where
  toFun : G → G
  upper : ∀ x y, dist (toFun x) (toFun y) ≤ K * dist x y + C
  lower : ∀ x y, dist x y ≤ K * dist (toFun x) (toFun y) + K * C
  surjective : ∀ y, ∃ x, dist y (toFun x) ≤ C

variable {G K C}

def SelfQuasiIsometry.inverse (f : SelfQuasiIsometry G K C) : G → G :=
  fun y => Classical.choose (f.surjective y)

theorem SelfQuasiIsometry.inverse_close (f : SelfQuasiIsometry G K C) (y : G) :
    dist y (f.toFun (f.inverse y)) ≤ C :=
  Classical.choose_spec (f.surjective y)

theorem SelfQuasiIsometry.left_inverse_close (f : SelfQuasiIsometry G K C)
    (hK : 0 ≤ K) (x : G) : dist (f.inverse (f.toFun x)) x ≤ 2 * K * C := by
  have h := f.lower x (f.inverse (f.toFun x))
  have hc := mul_le_mul_of_nonneg_left (f.inverse_close (f.toFun x)) hK
  rw [dist_comm] at h
  linarith

theorem SelfQuasiIsometry.inverse_upper (f : SelfQuasiIsometry G K C)
    (hK : 0 ≤ K) (x y : G) :
    dist (f.inverse x) (f.inverse y) ≤ K * dist x y + 3 * K * C := by
  have hd : dist (f.toFun (f.inverse x)) (f.toFun (f.inverse y)) ≤ dist x y + 2 * C := by
    have := dist_triangle4 (f.toFun (f.inverse x)) x y (f.toFun (f.inverse y))
    have hx := f.inverse_close x
    have hy := f.inverse_close y
    rw [dist_comm x] at hx
    linarith
  have := f.lower (f.inverse x) (f.inverse y)
  have := mul_le_mul_of_nonneg_left hd hK
  linarith

end PolycyclicRecognition

end

end OAI
