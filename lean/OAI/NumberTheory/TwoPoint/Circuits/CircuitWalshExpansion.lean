import OAI.NumberTheory.TwoPoint.Circuits.CircuitPolynomialAlgebra

namespace OAI

/-! Finite Walsh inversion and squared-error identities. These supply the
Fourier truncations used in the circuit approximation argument. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma walsh_kernel {n : ℕ} (x y : BooleanCube n) :
    (∑ S : Finset (Fin n), walsh S x * walsh S y) =
      if x = y then (2 : ℝ) ^ n else 0 := by
  have heq : (∑ S : Finset (Fin n), walsh S x * walsh S y) =
      ∏ i : Fin n, (1 + booleanSign (x i) * booleanSign (y i)) := by
    simp only [walsh, ← prod_mul_distrib]
    simpa using (prod_one_add (f := fun i : Fin n =>
      booleanSign (x i) * booleanSign (y i)) univ).symm
  rw [heq]
  by_cases hxy : x = y
  · subst y
    norm_num
  · rw [ite_eq_right hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      simpa only [funext_iff, not_forall] using hxy
    apply prod_eq_zero (mem_univ i)
    cases hx : x i <;> cases hy : y i <;> simp_all [booleanSign]

theorem walsh_inversion {n : ℕ} (f : BooleanCube n → ℝ) (x : BooleanCube n) :
    (∑ S : Finset (Fin n), walshCoefficient f S * walsh S x) = f x := by
  have heq : (∑ S : Finset (Fin n), walshCoefficient f S * walsh S x) =
      cubeAverage (fun y => f y * ∑ S : Finset (Fin n), walsh S y * walsh S x) := by
    simp only [mul_sum, cubeAverage_sum]
    apply sum_congr rfl
    intro S _
    unfold walshCoefficient
    have hp : (fun y => f y * (walsh S y * walsh S x)) =
        fun y => walsh S x * (f y * walsh S y) := by funext y; ring
    rw [hp, cubeAverage_mul_const, mul_comm]
  rw [heq]
  simp only [walsh_kernel, cubeAverage, mul_ite, mul_zero]
  simp [Fintype.card_bool, eq_comm]

theorem walsh_parseval {n : ℕ} (f : BooleanCube n → ℝ) :
    cubeAverage (fun x => (f x) ^ 2) =
      ∑ S : Finset (Fin n), (walshCoefficient f S) ^ 2 := by
  have heq : (fun x => (f x) ^ 2) = fun x =>
      ∑ S : Finset (Fin n), walshCoefficient f S * (f x * walsh S x) := by
    funext x
    calc
      _ = f x * (∑ S : Finset (Fin n), walshCoefficient f S * walsh S x) := by
        rw [walsh_inversion]
        ring
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro S _
        ring
  rw [heq, cubeAverage_sum]
  apply sum_congr rfl
  intro S _
  rw [cubeAverage_mul_const]
  change walshCoefficient f S * walshCoefficient f S = _
  ring

end TwoPointCorrelations

end OAI
