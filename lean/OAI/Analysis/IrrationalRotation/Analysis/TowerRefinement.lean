import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Tactic

namespace OAI

noncomputable section

open scoped BigOperators

namespace Invariant233.TowerRefinement

variable {A : Type*} [Semiring A] [StarRing A]

theorem matrixUnit_shift (U q : A) (i j r : ℕ) :
    U ^ i * (U ^ r * q * star (U ^ r)) * star (U ^ j) =
      U ^ (i + r) * q * star (U ^ (j + r)) := by
  simp only [pow_add, star_mul, mul_assoc]

theorem matrixUnit_decomposition {ι : Type*} (s : Finset ι)
    (U p : A) (q : ι → A) (offset : ι → ℕ)
    (hp : p = ∑ a ∈ s, U ^ offset a * q a * star (U ^ offset a))
    (i j : ℕ) :
    U ^ i * p * star (U ^ j) =
      ∑ a ∈ s, U ^ (i + offset a) * q a * star (U ^ (j + offset a)) := by
  rw [hp, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  exact matrixUnit_shift U (q a) i j (offset a)

variable {R : Type*} [CommSemiring R] [StarRing R] [Algebra R A] [StarModule R A]

theorem matrixUnit_mem_of_refinement {ι : Type*} (s : Finset ι)
    (B : StarSubalgebra R A) (U p : A) (q : ι → A)
    (offset height : ι → ℕ) (oldHeight : ℕ)
    (hp : p = ∑ a ∈ s, U ^ offset a * q a * star (U ^ offset a))
    (hfit : ∀ a ∈ s, offset a + oldHeight ≤ height a)
    (hq : ∀ a ∈ s, ∀ i j : ℕ, i < height a → j < height a →
      U ^ i * q a * star (U ^ j) ∈ B)
    {i j : ℕ} (hi : i < oldHeight) (hj : j < oldHeight) :
    U ^ i * p * star (U ^ j) ∈ B := by
  rw [matrixUnit_decomposition s U p q offset hp i j]
  apply B.sum_mem
  intro a ha
  have hbound := hfit a ha
  apply hq a ha <;> omega

def towerGenerators {ι : Type*} (U : A) (p : ι → A) (height : ι → ℕ) : Set A :=
  {x | ∃ a i j, i < height a ∧ j < height a ∧
    x = U ^ i * p a * star (U ^ j)}

theorem adjoin_towerGenerators_le_of_refinement
    {ι κ τ : Type*} (U : A) (p : ι → A) (q : κ → A)
    (oldHeight : ι → ℕ) (newHeight : κ → ℕ)
    (pieces : ι → Finset τ) (index : ι → τ → κ) (offset : ι → τ → ℕ)
    (hp : ∀ a, p a = ∑ b ∈ pieces a,
      U ^ offset a b * q (index a b) * star (U ^ offset a b))
    (hfit : ∀ a b, b ∈ pieces a →
      offset a b + oldHeight a ≤ newHeight (index a b)) :
    StarAlgebra.adjoin R (towerGenerators U p oldHeight) ≤
      StarAlgebra.adjoin R (towerGenerators U q newHeight) := by
  apply StarAlgebra.adjoin_le
  rintro x ⟨a, i, j, hi, hj, rfl⟩
  apply matrixUnit_mem_of_refinement (pieces a)
    (StarAlgebra.adjoin R (towerGenerators U q newHeight)) U (p a)
    (fun b => q (index a b)) (offset a) (fun b => newHeight (index a b))
    (oldHeight a) (hp a) (hfit a) _ hi hj
  intro b hb k l hk hl
  apply StarAlgebra.subset_adjoin
  exact ⟨index a b, k, l, hk, hl, rfl⟩

end Invariant233.TowerRefinement

end

end OAI
