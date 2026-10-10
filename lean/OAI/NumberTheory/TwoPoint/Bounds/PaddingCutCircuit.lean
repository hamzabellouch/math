import OAI.NumberTheory.TwoPoint.Bounds.PrimeDegreeCircuit
import OAI.NumberTheory.TwoPoint.Bounds.PaddingStateWeights

namespace OAI

/-! Arbitrary predicates of a bounded padding-prime state have a
literal depth-two DNF. Conjoining a fixed divisor costs one layer. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def activePredicateCircuit (n M : ℕ) (E : Finset (Fin n) → Prop) :
    AC0Circuit n :=
  AC0Circuit.disjunction (fun S : (boundedActiveStates n M).filter E =>
    activeStateCircuit S.val)

lemma activePredicateCircuit_eval (n M : ℕ) (E : Finset (Fin n) → Prop)
    (x : BooleanCube n) :
    (activePredicateCircuit n M E).eval x = true ↔
      (activeState x).card ≤ M ∧ E (activeState x) := by
  rw [activePredicateCircuit, AC0Circuit.disjunction_eval]
  constructor
  · rintro ⟨S, hS⟩
    have he := (activeStateCircuit_eval S.val x).mp hS
    have hm := mem_filter.mp S.property
    simpa only [he] using (And.intro (mem_boundedActiveStates.mp hm.1) hm.2)
  · intro hx
    refine ⟨⟨activeState x, mem_filter.mpr ⟨mem_boundedActiveStates.mpr hx.1, hx.2⟩⟩, ?_⟩
    exact (activeStateCircuit_eval _ _).mpr rfl

lemma activePredicateCircuit_depth (n M : ℕ) (E : Finset (Fin n) → Prop) :
    (activePredicateCircuit n M E).depth ≤ 2 :=
  AC0Circuit.disjunction_depth _ (fun S => activeStateCircuit_depth S.val)

lemma activePredicateCircuit_size (n M : ℕ) (E : Finset (Fin n) → Prop) :
    (activePredicateCircuit n M E).size ≤ 1 + (M + 1) * (n + 1) ^ (M + 1) := by
  rw [activePredicateCircuit, AC0Circuit.disjunction_size]
  simp only [activeStateCircuit_size, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hcard := (card_filter_le (boundedActiveStates n M) E).trans (boundedActiveStates_card n M)
  calc
    _ ≤ 1 + ((M + 1) * (n + 1) ^ M) * (1 + n) := by
      gcongr
      exact_mod_cast hcard
    _ = _ := by rw [pow_succ]; ring

noncomputable def stateDivisorCircuit {m n t : ℕ}
    (qindex : Fin n → Fin m) (dindex : Fin t → Fin m) (M : ℕ)
    (E : Finset (Fin n) → Prop) : AC0Circuit m :=
  AC0Circuit.conjunction (fun b : Bool => if b then
    AC0Circuit.relabel qindex (activePredicateCircuit n M E) else
    AC0Circuit.relabel dindex (degreeSubsetCircuit univ))

lemma stateDivisorCircuit_eval {m n t : ℕ}
    (qindex : Fin n → Fin m) (dindex : Fin t → Fin m) (M : ℕ)
    (E : Finset (Fin n) → Prop) (x : BooleanCube m) :
    (stateDivisorCircuit qindex dindex M E).eval x = true ↔
      (∀ i, x (dindex i) = true) ∧
        (activeState (fun i => x (qindex i))).card ≤ M ∧
          E (activeState (fun i => x (qindex i))) := by
  rw [stateDivisorCircuit, AC0Circuit.conjunction_eval]
  simp only [Bool.forall_bool, Bool.false_eq_true, ite_false, ite_true,
    AC0Circuit.relabel_eval, activePredicateCircuit_eval, degreeSubsetCircuit_eval]
  have he : (univ : Finset (Fin t)) ⊆ activeState (fun i => x (dindex i)) ↔
      ∀ i, x (dindex i) = true := by
    simp only [subset_iff, mem_univ, activeState, mem_filter, true_and, forall_const]
  rw [he]

lemma stateDivisorCircuit_depth {m n t : ℕ}
    (qindex : Fin n → Fin m) (dindex : Fin t → Fin m) (M : ℕ)
    (E : Finset (Fin n) → Prop) :
    (stateDivisorCircuit qindex dindex M E).depth ≤ 3 := by
  apply AC0Circuit.conjunction_depth
  intro b
  cases b
  · exact (AC0Circuit.relabel_depth _ _).trans ((degreeSubsetCircuit_depth _).trans (by omega))
  · exact (AC0Circuit.relabel_depth _ _).trans (activePredicateCircuit_depth _ _ _)

lemma stateDivisorCircuit_size {m n t : ℕ}
    (qindex : Fin n → Fin m) (dindex : Fin t → Fin m) (M : ℕ)
    (E : Finset (Fin n) → Prop) :
    (stateDivisorCircuit qindex dindex M E).size ≤
      3 + t + (M + 1) * (n + 1) ^ (M + 1) := by
  rw [stateDivisorCircuit, AC0Circuit.conjunction_size]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
  have hq := AC0Circuit.relabel_size qindex (activePredicateCircuit n M E)
  have hd := AC0Circuit.relabel_size dindex (degreeSubsetCircuit (univ : Finset (Fin t)))
  have hs := activePredicateCircuit_size n M E
  simp only [degreeSubsetCircuit_size, card_univ, Fintype.card_fin] at hd
  omega

lemma stateDivisorCircuit_size_exp {m n t : ℕ}
    (qindex : Fin n → Fin m) (dindex : Fin t → Fin m) (M : ℕ)
    (E : Finset (Fin n) → Prop) (L : ℝ) (hL : 4800 ≤ L)
    (hn : (n : ℝ) ≤ Real.exp L) (ht : (t : ℝ) ≤ 100 * Real.log L)
    (hM : (M : ℝ) ≤ 400 * Real.log L) :
    ((stateDivisorCircuit qindex dindex M E).size : ℝ) ≤ Real.exp (L ^ 3) := by
  have hL0 : 0 ≤ L := by linarith
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hML : (M : ℝ) + 1 ≤ 401 * L := by nlinarith
  have htwo : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hn' : (n : ℝ) + 1 ≤ Real.exp (2 * L) := by
    rw [show 2 * L = L + L by ring, Real.exp_add]
    nlinarith
  have hprod : ((M : ℝ) + 1) * ((n : ℝ) + 1) ^ (M + 1) ≤
      Real.exp (1203 * L ^ 2) := by
    have heM : (M : ℝ) + 1 ≤ Real.exp ((M : ℝ) + 1) := by
      linarith [Real.add_one_le_exp ((M : ℝ) + 1)]
    calc
      _ ≤ Real.exp ((M : ℝ) + 1) * (Real.exp (2 * L)) ^ (M + 1) :=
        mul_le_mul heM
          (pow_le_pow_left₀ (by positivity) hn' _) (by positivity) (by positivity)
      _ = Real.exp (((M : ℝ) + 1) * (1 + 2 * L)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        push_cast
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hm := mul_le_mul_of_nonneg_right hML (show 0 ≤ 1 + 2 * L by positivity)
        have hs := mul_nonneg hL0 (show 0 ≤ L - 1 by linarith)
        nlinarith)
  have hsmall : 3 + (t : ℝ) ≤ Real.exp (1203 * L ^ 2) := by
    have he := Real.add_one_le_exp (1203 * L ^ 2)
    nlinarith [sq_nonneg (L - 1)]
  have hc : ((stateDivisorCircuit qindex dindex M E).size : ℝ) ≤
      3 + t + ((M : ℝ) + 1) * ((n : ℝ) + 1) ^ (M + 1) := by
    exact_mod_cast stateDivisorCircuit_size qindex dindex M E
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

lemma stateDivisorCircuit_integer (U Q : Finset ℕ) (hQU : Q ⊆ U)
    (hQ : ∀ p ∈ Q, p.Prime) (q : ℕ) (hq : q ∈ retainedPrimeDivisors Q)
    (M : ℕ) (E : Finset (Fin (Fintype.card Q)) → Prop) (n : ℤ) :
    (stateDivisorCircuit (primeSubsetIndex U Q hQU)
      (primeSubsetIndex U q.primeFactors ((retainedPrimeDivisor_factors Q hQ hq).trans hQU))
      M E).eval (primeSiteBits U n) = true ↔
        (q : ℤ) ∣ n ∧ actualPaddingDegree Q n ≤ M ∧
          E (paddingActiveState Q (Fintype.equivFin Q).symm n) := by
  rw [stateDivisorCircuit_eval, prime_divisor_all_bits U Q hQU hQ q hq n,
    primeSubsetIndex_bits, primeSiteBits_card]
  rfl

end TwoPointCorrelations

end OAI
