import Mathlib

namespace OAI

noncomputable section
namespace EuclideanRamsey

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def Congruent {s d D : ℕ} (a : Fin s → Space d) (b : Fin s → Space D) : Prop :=
  ∀ i j, dist (b i) (b j) = dist (a i) (a j)

def Ramsey {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ c : Space D → Fin r, ∃ b : Fin s → Space D,
      Congruent a b ∧ ∃ k : Fin r, ∀ i, c (b i) = k

namespace NineStatement

def literalCircleConfig (t : Fin 9 → ℝ) (i : Fin 9) : Space 2 :=
  WithLp.toLp 2 ![(1 - (t i)^2) / (1 + (t i)^2),
    (2 * t i) / (1 + (t i)^2)]

/-- Nine algebraically independent real parameters give distinct unit-circle
points whose configuration is not Ramsey. -/
theorem nine_circle_configuration (t : Fin 9 → ℝ)
    (ht : AlgebraicIndependent ℚ t) :
    Function.Injective (literalCircleConfig t) ∧
      (∀ i, dist (literalCircleConfig t i) 0 = 1) ∧
      ¬ Ramsey (literalCircleConfig t) := by
  sorry

end NineStatement
end EuclideanRamsey

end

end OAI
