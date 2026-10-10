import OAI.NumberTheory.TwoPoint.Bounds.MertensScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! The fixed modulus-five prime-number input used by the manuscript.

Published source: D. Koukoulopoulos, *The Distribution of Prime Numbers*,
AMS, 2019, Theorem 12.1 (Siegel--Walfisz), with modulus 5 fixed. That theorem
is stated for the prime-counting function. `ModFiveThetaInput` is its standard
partial-summation consequence for the logarithmically weighted prime count,
specialized to the two selections needed here. The complementary selection
includes the single prime 5, which changes the error by a bounded amount.
Source: https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf

The estimate includes every prime in the selected classes. Removing a finite
exceptional prime set contributes an explicit finite-deletion correction.
-/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical Topology

def ModFivePrime (one : Bool) (p : ℕ) : Prop :=
  p.Prime ∧ if one then p % 5 = 1 else p % 5 ≠ 1

noncomputable def modFiveDensity (one : Bool) : ℝ := if one then 1 / 4 else 3 / 4

noncomputable def modFivePrimesUpTo (one : Bool) (x : ℝ) : Finset ℕ :=
  (Icc 0 ⌊x⌋₊).filter (ModFivePrime one)

noncomputable def modFiveLogWeight (one : Bool) (p : ℕ) : ℝ :=
  if ModFivePrime one p then Real.log p else 0

noncomputable def modFiveTheta (one : Bool) (x : ℝ) : ℝ :=
  ∑ p ∈ Icc 0 ⌊x⌋₊, modFiveLogWeight one p

noncomputable def deletedModFivePrimes (E : Finset ℕ) (one : Bool) (x : ℝ) : Finset ℕ :=
  modFivePrimesUpTo one x \ E

noncomputable def deletedModFiveTheta (E : Finset ℕ) (one : Bool) (x : ℝ) : ℝ :=
  ∑ p ∈ deletedModFivePrimes E one x, Real.log p

/-- The precise published input: a fixed-modulus consequence of
Koukoulopoulos, Theorem 12.1, before any application-dependent exclusions. -/
def ModFiveThetaInput : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (one : Bool) (x : ℝ), 2 ≤ x →
    |modFiveTheta one x - modFiveDensity one * x| ≤
      C * x * Real.exp (-c * Real.sqrt (Real.log x))

lemma modFiveTheta_eq_sum (one : Bool) (x : ℝ) :
    modFiveTheta one x = ∑ p ∈ modFivePrimesUpTo one x, Real.log p := by
  simp [modFiveTheta, modFivePrimesUpTo, modFiveLogWeight, sum_filter]

lemma modFivePrimesUpTo_prime {one : Bool} {x : ℝ} {p : ℕ}
    (hp : p ∈ modFivePrimesUpTo one x) : p.Prime :=
  (mem_filter.mp hp).2.1

lemma modFivePrimesUpTo_le {one : Bool} {x : ℝ} (hx : 0 ≤ x) {p : ℕ}
    (hp : p ∈ modFivePrimesUpTo one x) : (p : ℝ) ≤ x :=
  (Nat.le_floor_iff hx).mp (mem_Icc.mp (mem_filter.mp hp).1).2

lemma modFivePrimesUpTo_mono (one : Bool) {x y : ℝ} (hxy : x ≤ y) :
    modFivePrimesUpTo one x ⊆ modFivePrimesUpTo one y := by
  intro p hp
  obtain ⟨hp, hsel⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hp).1,
    (mem_Icc.mp hp).2.trans (Nat.floor_le_floor hxy)⟩, hsel⟩

lemma modFivePrimesUpTo_disjoint (x y : ℝ) :
    Disjoint (modFivePrimesUpTo true x) (modFivePrimesUpTo false y) := by
  apply disjoint_left.mpr
  intro p hp hq
  have hp' := (mem_filter.mp hp).2.2
  have hq' := (mem_filter.mp hq).2.2
  change p % 5 = 1 at hp'
  change p % 5 ≠ 1 at hq'
  exact hq' hp'

lemma log_nat_nonneg (p : ℕ) : 0 ≤ Real.log (p : ℝ) := by
  by_cases hp : p = 0
  · simp [hp]
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp)

/-- The entire cost of removing a finite exceptional prime set is explicit. -/
lemma deletedModFiveTheta_error (E : Finset ℕ) (one : Bool) (x : ℝ) :
    |deletedModFiveTheta E one x - modFiveTheta one x| ≤
      ∑ p ∈ E, Real.log p := by
  rw [modFiveTheta_eq_sum]
  have he : deletedModFiveTheta E one x -
      (∑ p ∈ modFivePrimesUpTo one x, Real.log p) =
      -(∑ p ∈ modFivePrimesUpTo one x ∩ E, Real.log p) := by
    unfold deletedModFiveTheta deletedModFivePrimes
    have hs := sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ))
      (inter_subset_left : modFivePrimesUpTo one x ∩ E ⊆ modFivePrimesUpTo one x)
    rw [sdiff_inter_self_left] at hs
    linarith
  rw [he, abs_neg, abs_of_nonneg (sum_nonneg (fun p _ => log_nat_nonneg p))]
  exact sum_le_sum_of_subset_of_nonneg inter_subset_right (fun p _ _ => log_nat_nonneg p)

theorem ModFiveThetaInput.deleted_error (hP : ModFiveThetaInput) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (E : Finset ℕ) (one : Bool) (x : ℝ), 2 ≤ x →
      |deletedModFiveTheta E one x - modFiveDensity one * x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) + ∑ p ∈ E, Real.log p := by
  obtain ⟨c, C, hc, hC, h⟩ := hP
  refine ⟨c, C, hc, hC, fun E one x hx => ?_⟩
  calc
    _ = |(modFiveTheta one x - modFiveDensity one * x) +
        (deletedModFiveTheta E one x - modFiveTheta one x)| := by congr 1; ring
    _ ≤ |modFiveTheta one x - modFiveDensity one * x| +
        |deletedModFiveTheta E one x - modFiveTheta one x| := abs_add_le _ _
    _ ≤ _ := add_le_add (h one x hx) (deletedModFiveTheta_error E one x)

end TwoPointCorrelations

end OAI
