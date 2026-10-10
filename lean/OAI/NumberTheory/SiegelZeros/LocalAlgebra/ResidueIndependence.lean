import Mathlib.Algebra.Algebra.Rat
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.SimpleRing.Basic

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.Workers.W14

open scoped BigOperators

theorem integer_relation_eq_zero {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V] {c : ι → V}
    (hc : LinearIndependent ℚ c) (n : ι → ℤ)
    (h : ∑ i, (n i : ℚ) • c i = 0) : ∀ i, n i = 0 := by
  have hn := Fintype.linearIndependent_iff.mp hc (fun i => (n i : ℚ)) h
  intro i
  exact Int.cast_eq_zero.mp (hn i)

theorem complex_integer_relation_eq_zero {ι : Type*} [Fintype ι]
    {c : ι → ℂ} (hc : LinearIndependent ℚ c) (n : ι → ℤ)
    (h : ∑ i, c i * (n i : ℂ) = 0) : ∀ i, n i = 0 := by
  apply integer_relation_eq_zero hc n
  simpa [Rat.smul_def, mul_comm] using h

theorem residue_field_integer_relation_eq_zero {ι K : Type*} [Fintype ι]
    [Field K] {c : ι → ℂ} (hc : LinearIndependent ℚ c)
    (constants : ℂ →+* K) (n : ι → ℤ)
    (h : ∑ i, constants (c i) * (n i : K) = 0) : ∀ i, n i = 0 := by
  apply complex_integer_relation_eq_zero hc n
  apply constants.injective
  simpa using h

theorem orders_eq_zero_of_residue_equations {ι E : Type*} [Fintype ι]
    {c : ι → ℂ} (hc : LinearIndependent ℚ c) (ord : E → ι → ℤ)
    (hres : ∀ e, ∑ i, c i * (ord e i : ℂ) = 0) :
    ∀ e i, ord e i = 0 := by
  intro e
  exact complex_integer_relation_eq_zero hc (ord e) (hres e)

theorem residue_ne_zero_of_order_ne_zero {ι : Type*} [Fintype ι]
    {c : ι → ℂ} (hc : LinearIndependent ℚ c) (n : ι → ℤ)
    {i : ι} (hi : n i ≠ 0) : ∑ j, c j * (n j : ℂ) ≠ 0 := by
  intro hz
  exact hi (complex_integer_relation_eq_zero hc n hz i)

theorem four_orders_eq_zero {E : Type*} {c : Fin 4 → ℂ}
    (hc : LinearIndependent ℚ c) (ord : E → Fin 4 → ℤ)
    (hres : ∀ e, ∑ i, c i * (ord e i : ℂ) = 0) :
    ∀ e i, ord e i = 0 :=
  orders_eq_zero_of_residue_equations hc ord hres

end SiegelZerosAwei.Workers.W14

end

end SiegelZeros

end OAI
