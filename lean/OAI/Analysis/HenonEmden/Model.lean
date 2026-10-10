import Mathlib

namespace OAI

namespace HenonLaneEmden

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

structure IsSolution (n : ℕ) (p q A B : ℝ) (u v : Space n → ℝ) : Prop where
  continuous_u : Continuous u
  continuous_v : Continuous v
  regular_u : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))
  regular_v : ContDiffOn ℝ 2 v ({0}ᶜ : Set (Space n))
  positive_u : ∀ x, 0 < u x
  positive_v : ∀ x, 0 < v x
  equation_u : ∀ x, x ≠ 0 →
    -(Laplacian.laplacian u) x = Real.rpow ‖x‖ A * Real.rpow (v x) p
  equation_v : ∀ x, x ≠ 0 →
    -(Laplacian.laplacian v) x = Real.rpow ‖x‖ B * Real.rpow (u x) q

def Subcritical (n : ℕ) (p q A B : ℝ) : Prop :=
  ((n : ℝ) + A) / (p + 1) + ((n : ℝ) + B) / (q + 1) > (n : ℝ) - (1 + 1)

end HenonLaneEmden

end OAI
