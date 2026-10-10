import OAI.NumberTheory.TwoPoint.Bounds.DegreeThresholdCircuit
import OAI.NumberTheory.TwoPoint.Bounds.PrimeLiteralEncoding
import OAI.NumberTheory.TwoPoint.Bounds.PaddingActiveState

namespace OAI

/-! Literal degree deletion together with divisibility by a fixed
padding divisor. All tests use the common prime coordinates. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def primeSubsetIndex (U S : Finset ℕ) (hS : S ⊆ U) :
    Fin (Fintype.card S) → Fin (Fintype.card U) :=
  fun i => (Fintype.equivFin U)
    ⟨((Fintype.equivFin S).symm i).val, hS ((Fintype.equivFin S).symm i).property⟩

lemma primeSubsetIndex_value (U S : Finset ℕ) (hS : S ⊆ U)
    (i : Fin (Fintype.card S)) :
    ((Fintype.equivFin U).symm (primeSubsetIndex U S hS i)).val =
      ((Fintype.equivFin S).symm i).val := by
  simp only [primeSubsetIndex, Equiv.symm_apply_apply]

noncomputable def primeSiteBits (U : Finset ℕ) (n : ℤ) :
    BooleanCube (Fintype.card U) :=
  fun i => decide ((((Fintype.equivFin U).symm i).val : ℤ) ∣ n)

lemma primeSubsetIndex_bits (U S : Finset ℕ) (hS : S ⊆ U) (n : ℤ) :
    (fun i => primeSiteBits U n (primeSubsetIndex U S hS i)) = primeSiteBits S n := by
  funext i
  simp only [primeSiteBits, primeSubsetIndex_value]

lemma primeSiteBits_card (U : Finset ℕ) (n : ℤ) :
    (activeState (primeSiteBits U n)).card = actualPaddingDegree U n :=
  paddingActiveState_card U (Fintype.equivFin U).symm n

noncomputable def degreeDivisorCircuit {m n t : ℕ}
    (pindex : Fin n → Fin m) (qindex : Fin t → Fin m) (r : ℕ) : AC0Circuit m :=
  AC0Circuit.conjunction (fun b : Bool => if b then
    AC0Circuit.relabel pindex (degreeThresholdCircuit n r) else
    AC0Circuit.relabel qindex (degreeSubsetCircuit univ))

lemma degreeDivisorCircuit_eval {m n t : ℕ}
    (pindex : Fin n → Fin m) (qindex : Fin t → Fin m) (r : ℕ)
    (x : BooleanCube m) :
    (degreeDivisorCircuit pindex qindex r).eval x = true ↔
      (∀ i, x (qindex i) = true) ∧ r ≤ (activeState (fun i => x (pindex i))).card := by
  rw [degreeDivisorCircuit, AC0Circuit.conjunction_eval]
  simp only [Bool.forall_bool, Bool.false_eq_true, ite_false, ite_true,
    AC0Circuit.relabel_eval, degreeThresholdCircuit_eval, degreeSubsetCircuit_eval]
  have he : (univ : Finset (Fin t)) ⊆ activeState (fun i => x (qindex i)) ↔
      ∀ i, x (qindex i) = true := by
    simp only [subset_iff, mem_univ, activeState, mem_filter, true_and, forall_const]
  rw [he]

lemma degreeDivisorCircuit_depth {m n t : ℕ}
    (pindex : Fin n → Fin m) (qindex : Fin t → Fin m) (r : ℕ) :
    (degreeDivisorCircuit pindex qindex r).depth ≤ 3 := by
  apply AC0Circuit.conjunction_depth
  intro b
  cases b
  · exact (AC0Circuit.relabel_depth _ _).trans ((degreeSubsetCircuit_depth _).trans (by omega))
  · exact (AC0Circuit.relabel_depth _ _).trans (degreeThresholdCircuit_depth _ _)

lemma degreeDivisorCircuit_size {m n t : ℕ}
    (pindex : Fin n → Fin m) (qindex : Fin t → Fin m) (r : ℕ) :
    (degreeDivisorCircuit pindex qindex r).size ≤
      3 + t + (r + 1) * (n + 1) ^ r := by
  rw [degreeDivisorCircuit, AC0Circuit.conjunction_size]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
  have hq := AC0Circuit.relabel_size qindex (degreeSubsetCircuit (univ : Finset (Fin t)))
  have hp := AC0Circuit.relabel_size pindex (degreeThresholdCircuit n r)
  have hd := degreeThresholdCircuit_size_le n r
  simp only [degreeSubsetCircuit_size, card_univ, Fintype.card_fin] at hq
  omega

lemma degreeDivisorCircuit_size_exp {m n t : ℕ}
    (pindex : Fin n → Fin m) (qindex : Fin t → Fin m) (r : ℕ) (L : ℝ)
    (hL : 4800 ≤ L) (hn : (n : ℝ) ≤ Real.exp L)
    (ht : (t : ℝ) ≤ 100 * Real.log L) (hr : (r : ℝ) ≤ 400 * Real.log L + 1) :
    ((degreeDivisorCircuit pindex qindex r).size : ℝ) ≤ Real.exp (L ^ 3) := by
  have hL0 : 0 ≤ L := by linarith
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hrL : (r : ℝ) ≤ 401 * L := by nlinarith
  have htwo : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hn' : (n : ℝ) + 1 ≤ Real.exp (2 * L) := by
    rw [show 2 * L = L + L by ring, Real.exp_add]
    nlinarith
  have hprod : ((r : ℝ) + 1) * ((n : ℝ) + 1) ^ r ≤
      Real.exp (1203 * L ^ 2) := by
    calc
      _ ≤ Real.exp (r : ℝ) * (Real.exp (2 * L)) ^ r :=
        mul_le_mul (Real.add_one_le_exp (r : ℝ))
          (pow_le_pow_left₀ (by positivity) hn' r) (by positivity) (by positivity)
      _ = Real.exp ((r : ℝ) * (1 + 2 * L)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hm := mul_le_mul_of_nonneg_right hrL (show 0 ≤ 1 + 2 * L by positivity)
        have hs := mul_nonneg hL0 (show 0 ≤ L - 1 by linarith)
        nlinarith)
  have hsmall : 3 + (t : ℝ) ≤ Real.exp (1203 * L ^ 2) := by
    have he := Real.add_one_le_exp (1203 * L ^ 2)
    nlinarith [sq_nonneg (L - 1)]
  have hc : ((degreeDivisorCircuit pindex qindex r).size : ℝ) ≤
      3 + t + ((r : ℝ) + 1) * ((n : ℝ) + 1) ^ r := by
    exact_mod_cast degreeDivisorCircuit_size pindex qindex r
  calc
    _ ≤ 2 * Real.exp (1203 * L ^ 2) := by linarith
    _ ≤ Real.exp (1 + 1203 * L ^ 2) := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hsq : (1 : ℝ) ≤ L ^ 2 := by nlinarith
      have hh := mul_nonneg (sq_nonneg L) (show 0 ≤ L - 1204 by linarith)
      nlinarith)

lemma prime_divisor_all_bits (U Q : Finset ℕ) (hQU : Q ⊆ U)
    (hQ : ∀ p ∈ Q, p.Prime) (q : ℕ) (hq : q ∈ retainedPrimeDivisors Q) (n : ℤ) :
    (∀ i : Fin (Fintype.card q.primeFactors),
      primeSiteBits U n (primeSubsetIndex U q.primeFactors
        ((retainedPrimeDivisor_factors Q hQ hq).trans hQU) i) = true) ↔
      (q : ℤ) ∣ n := by
  rw [← padding_literal_support_iff_dvd Q hQ n q hq, paddingAvailablePrimes_integer]
  constructor
  · intro hb p hp
    let i := (Fintype.equivFin q.primeFactors) ⟨p, hp⟩
    have hi := hb i
    simp only [primeSiteBits, primeSubsetIndex_value, i, Equiv.symm_apply_apply,
      decide_eq_true_eq] at hi
    exact mem_filter.mpr ⟨retainedPrimeDivisor_factors Q hQ hq hp, hi⟩
  · intro hb i
    have hh := hb ((Fintype.equivFin q.primeFactors).symm i).property
    simpa only [primeSiteBits, primeSubsetIndex_value, decide_eq_true_eq] using (mem_filter.mp hh).2

lemma degreeDivisorCircuit_integer (U P Q : Finset ℕ) (hPU : P ⊆ U)
    (hQU : Q ⊆ U) (hQ : ∀ p ∈ Q, p.Prime) (q : ℕ)
    (hq : q ∈ retainedPrimeDivisors Q) (T : ℝ) (hT : 0 ≤ T) (n : ℤ) :
    (degreeDivisorCircuit (primeSubsetIndex U P hPU)
      (primeSubsetIndex U q.primeFactors ((retainedPrimeDivisor_factors Q hQ hq).trans hQU))
      (⌊T⌋₊ + 1)).eval (primeSiteBits U n) = true ↔
        (q : ℤ) ∣ n ∧ T < (actualPaddingDegree P n : ℝ) := by
  rw [degreeDivisorCircuit_eval, prime_divisor_all_bits U Q hQU hQ q hq n,
    primeSubsetIndex_bits, primeSiteBits_card, ← Nat.lt_iff_add_one_le, Nat.floor_lt hT]

end TwoPointCorrelations

end OAI
