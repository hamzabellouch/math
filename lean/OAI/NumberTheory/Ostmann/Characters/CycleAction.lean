import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import OAI.NumberTheory.Ostmann.Tree.FiniteActionAverage

namespace OAI

/-!
# Reciprocal multiplication on cycle leaves

An integer sign on each leaf specifies multiplication by `z` or its inverse.
A block whose signs sum to zero has its product preserved by this action.
Thus a balanced cycle preserves both component totals and quartet totals.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

def cycleMultiply {I G : Type*} [CommGroup G] (sign : I → ℤ) (z : G) (m : I → G) : I → G :=
  fun i => z ^ sign i * m i

@[instance_reducible] def leafCycleAction {I G : Type*} [CommGroup G] (sign : I → ℤ) : MulAction G (I → G) where
  smul := cycleMultiply sign
  one_smul m := by
    change cycleMultiply sign 1 m = m
    funext i
    change (1 : G) ^ sign i * m i = m i
    simp
  mul_smul z w m := by
    change cycleMultiply sign (z * w) m = cycleMultiply sign z (cycleMultiply sign w m)
    funext i
    change (z * w) ^ sign i * m i = z ^ sign i * (w ^ sign i * m i)
    rw [mul_zpow, mul_assoc]

theorem cycleMultiply_product {I G : Type*} [CommGroup G]
    (s : Finset I) (sign : I → ℤ) (z : G) (m : I → G) :
    (∏ i ∈ s, cycleMultiply sign z m i) = z ^ (∑ i ∈ s, sign i) * ∏ i ∈ s, m i := by
  classical
  have hp : (∏ i ∈ s, z ^ sign i) = z ^ (∑ i ∈ s, sign i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, ih, zpow_add]
  simp only [cycleMultiply, Finset.prod_mul_distrib, hp]

theorem cycleMultiply_preserves_product {I G : Type*} [CommGroup G]
    (s : Finset I) (sign : I → ℤ) (hs : ∑ i ∈ s, sign i = 0) (z : G) (m : I → G) :
    (∏ i ∈ s, cycleMultiply sign z m i) = ∏ i ∈ s, m i := by
  rw [cycleMultiply_product, hs, zpow_zero, one_mul]

noncomputable def cycleAverage {I G : Type*} [CommGroup G] [Fintype G]
    (sign : I → ℤ) (f : (I → G) → ℂ) (m : I → G) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ z : G, f (cycleMultiply sign z m)

theorem cycleAverage_energy_le {I G : Type*} [CommGroup G] [Fintype G] [Fintype I] [DecidableEq I]
    (sign : I → ℤ) (f : (I → G) → ℂ) :
    (∑ m : I → G, ‖cycleAverage sign f m‖ ^ 2) ≤ ∑ m : I → G, ‖f m‖ ^ 2 := by
  let := leafCycleAction (G := G) sign
  exact finiteActionAverage_energy_le (G := G) f

/-- Tests depending only on balanced block products are unchanged by projection. -/
theorem cycleAverage_block_correlation {I J G : Type*} [CommGroup G]
    [Fintype G] [Fintype I] [DecidableEq I]
    (blocks : J → Finset I) (sign : I → ℤ)
    (hs : ∀ j, ∑ i ∈ blocks j, sign i = 0)
    (f : (I → G) → ℂ) (h : (J → G) → ℂ) :
    (∑ m : I → G, cycleAverage sign f m * conj (h (fun j => ∏ i ∈ blocks j, m i))) =
      ∑ m : I → G, f m * conj (h (fun j => ∏ i ∈ blocks j, m i)) := by
  let := leafCycleAction (G := G) sign
  apply finiteActionAverage_correlation (G := G)
  intro z m
  congr 1
  funext j
  exact cycleMultiply_preserves_product (blocks j) sign (hs j) z m

end Ostmann

end OAI
