import OAI.NumberTheory.TwoPoint.Circuits.CircuitSemiExact
import OAI.NumberTheory.TwoPoint.Bounds.PaddingSelectionLaw

namespace OAI

/-! The finite sampling calculation in the circuit approximation: a random
subset hits a prescribed nonempty set exactly once with probability
`k*p*(1-p)^(k-1)`. No asymptotic input is used. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def bernoulliCubeLaw (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteLaw (BooleanCube n) :=
  FiniteLaw.independent (fun _ : Fin n => booleanLaw p hp hp1)

lemma bernoulliCubeLaw_pattern (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset (Fin n)) (z : BooleanCube n) :
    (bernoulliCubeLaw n p hp hp1).average (cubePattern S z) =
      ∏ i ∈ S, (if z i then p else 1 - p) := by
  let F := fun i : Fin n => fun b : Bool =>
    if i ∈ S then (if b = z i then (1 : ℝ) else 0) else 1
  have heq (x : BooleanCube n) : cubePattern S z x = ∏ i, F i (x i) := by
    dsimp only [F]
    rw [Fintype.prod_ite_mem, prod_boole]
    unfold cubePattern
    split_ifs <;> rfl
  have hlocal (i : Fin n) : (booleanLaw p hp hp1).average (F i) =
      if i ∈ S then (if z i then p else 1 - p) else 1 := by
    by_cases hi : i ∈ S
    · cases hz : z i <;> simp [FiniteLaw.average, booleanLaw, F, hi, hz]
    · simp [F, hi]
  have hfun : cubePattern S z = fun x => ∏ i, F i (x i) := funext heq
  rw [hfun]
  change (FiniteLaw.independent (fun _ : Fin n => booleanLaw p hp hp1)).average
    (fun x => ∏ i, F i (x i)) = _
  rw [FiniteLaw.independent_average_product]
  simp_rw [hlocal]
  exact Fintype.prod_ite_mem S _

def singleBitPattern {n : ℕ} (i : Fin n) : BooleanCube n := fun j => decide (j = i)

noncomputable def singleHitScore {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) : ℝ :=
  ∑ i ∈ S, cubePattern S (singleBitPattern i) x

lemma bernoulliCubeLaw_singleHitScore (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset (Fin n)) :
    (bernoulliCubeLaw n p hp hp1).average (singleHitScore S) =
      (S.card : ℝ) * p * (1 - p) ^ (S.card - 1) := by
  have hterm (i : Fin n) (hi : i ∈ S) :
      (bernoulliCubeLaw n p hp hp1).average (cubePattern S (singleBitPattern i)) =
        p * (1 - p) ^ (S.card - 1) := by
    rw [bernoulliCubeLaw_pattern, ← prod_erase_mul _ _ hi]
    have hprod : (∏ j ∈ S.erase i, if singleBitPattern i j then p else 1 - p) =
        (1 - p) ^ (S.card - 1) := by
      have heq : (∏ j ∈ S.erase i, if singleBitPattern i j then p else 1 - p) =
          ∏ _j ∈ S.erase i, (1 - p) := by
        apply prod_congr rfl
        intro j hj
        simp [singleBitPattern, (mem_erase.mp hj).1]
      rw [heq, prod_const, card_erase_of_mem hi]
    rw [hprod]
    simp [singleBitPattern, mul_comm]
  have heq : (bernoulliCubeLaw n p hp hp1).average (singleHitScore S) =
      ∑ i ∈ S, (bernoulliCubeLaw n p hp hp1).average (cubePattern S (singleBitPattern i)) := by
    unfold singleHitScore FiniteLaw.average
    simp only [mul_sum]
    rw [sum_comm]
  rw [heq, sum_congr rfl (fun i hi => hterm i hi)]
  simp [mul_assoc]

/-- A dyadic sampling scale with expected hit count between 1/4 and 1/2
has a uniformly positive chance of isolating one marked coordinate. -/
lemma single_hit_probability_lower (k : ℕ) (hk : 0 < k) (p : ℝ)
    (hp : 0 ≤ p) (hsmall : (k : ℝ) * p ≤ 1 / 2)
    (hlarge : 1 / 4 ≤ (k : ℝ) * p) :
    1 / 8 ≤ (k : ℝ) * p * (1 - p) ^ (k - 1) := by
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpone : p ≤ 1 := by nlinarith
  have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ -p by linarith) (k - 1)
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk, Nat.cast_one]
  have hpow : (1 / 2 : ℝ) ≤ (1 - p) ^ (k - 1) := by
    rw [hkcast] at hbern
    have heq : 1 + -p = 1 - p := by ring
    rw [heq] at hbern
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hpow (mul_nonneg (Nat.cast_nonneg k) hp)
  nlinarith

end TwoPointCorrelations

end OAI
