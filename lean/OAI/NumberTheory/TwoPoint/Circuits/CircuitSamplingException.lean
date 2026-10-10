import OAI.NumberTheory.TwoPoint.Circuits.CircuitIsolationEvent

namespace OAI

/-! The exceptional event is expressed by the single-hit circuits, so it
can itself be approximated by Fourier truncation in the next stage. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma isolatesOne_false_iff {k : ℕ} (b mask : BooleanCube k) :
    isolatesOne (falseCoordinates b) mask ↔
      ∃ i : sampledCoordinates mask, b i = false ∧
        ∀ j : sampledCoordinates mask, j ≠ i → b j = true := by
  constructor
  · rintro ⟨i, hi, hm⟩
    have hbi : b i = false := (mem_filter.mp hi).2
    have hmi : mask i = true := by simpa [singleBitPattern] using hm i hi
    let v : sampledCoordinates mask := ⟨i, by simp [sampledCoordinates, hmi]⟩
    refine ⟨v, hbi, ?_⟩
    intro j hji
    have hval : j.val ≠ i := fun h => hji (Subtype.ext h)
    have hmj : mask j = true := (mem_filter.mp j.property).2
    cases hb : b j
    · have hj : j.val ∈ falseCoordinates b := by simp [falseCoordinates, hb]
      have ht := hm j hj
      simp [singleBitPattern, hval, hmj] at ht
    · rfl
  · rintro ⟨i, hbi, hj⟩
    refine ⟨i, by simp [falseCoordinates, hbi], ?_⟩
    intro j hjfalse
    have hbj : b j = false := (mem_filter.mp hjfalse).2
    by_cases hji : j = i.val
    · subst j
      have hmi : mask i = true := (mem_filter.mp i.property).2
      simpa [singleBitPattern] using hmi
    · have hmj : mask j = false := by
        cases hmask : mask j
        · rfl
        · let v : sampledCoordinates mask := ⟨j, by simp [sampledCoordinates, hmask]⟩
          have hne : v ≠ i := fun h => hji (congrArg Subtype.val h)
          have htrue := hj v hne
          rw [show b v = false from hbj] at htrue
          contradiction
      simp [singleBitPattern, hji, hmj]

namespace AC0Circuit

noncomputable def gateSamplingException {n k s : ℕ}
    (sample : GateSamplingChoices k k s) (c : Fin k → AC0Circuit n) : AC0Circuit n :=
  conjunction (fun flag : Bool => if flag then
    (certificateDisjunction (fun j : Fin (Nat.log 2 k + 3) × Fin s =>
      uniqueFalseCircuit c (sampledCoordinates (sample j.1 j.2)))).negate
    else (andGate c).negate)

lemma gateSamplingException_eval {n k s : ℕ}
    (sample : GateSamplingChoices k k s) (c : Fin k → AC0Circuit n)
    (x : BooleanCube n) :
    (gateSamplingException sample c).eval x = true ↔
      (¬∀ i, (c i).eval x = true) ∧
        ∀ a j, ¬isolatesOne (falseCoordinates (fun i => (c i).eval x)) (sample a j) := by
  simp only [gateSamplingException, conjunction_eval, Bool.forall_bool, Bool.false_eq_true,
    ite_false, ite_true, negate_eval, ne_eq, certificateDisjunction_eval, uniqueFalseCircuit_eval,
    eval, decide_eq_true_eq, not_exists, Prod.forall, isolatesOne_false_iff]

lemma gateSamplingException_depth {n k s d : ℕ}
    (sample : GateSamplingChoices k k s) (c : Fin k → AC0Circuit n)
    (hc : ∀ i, (c i).depth ≤ d) :
    (gateSamplingException sample c).depth ≤ d + 4 := by
  apply conjunction_depth
  intro flag
  cases flag
  · simp only [Bool.false_eq_true, ite_false, negate_depth, depth]
    have h := Finset.sup_le (fun i (_ : i ∈ univ) => hc i)
    omega
  · simp only [ite_true, negate_depth]
    apply certificateDisjunction_depth
    intro j
    exact uniqueFalseCircuit_depth c hc _

lemma gateSamplingException_size {n k s : ℕ}
    (sample : GateSamplingChoices k k s) (c : Fin k → AC0Circuit n) :
    (gateSamplingException sample c).size ≤
      3 + (∑ i, (c i).size) + s * (Nat.log 2 k + 3) *
        (1 + k * (1 + ∑ i, (c i).size)) := by
  rw [gateSamplingException, conjunction_size]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true, negate_size,
    certificateDisjunction_size, size]
  have hsum : (∑ j : Fin (Nat.log 2 k + 3) × Fin s,
      (uniqueFalseCircuit c (sampledCoordinates (sample j.1 j.2))).size) ≤
        s * (Nat.log 2 k + 3) * (1 + k * (1 + ∑ i, (c i).size)) := by
    calc
      _ ≤ ∑ _j : Fin (Nat.log 2 k + 3) × Fin s,
          (1 + k * (1 + ∑ i, (c i).size)) :=
        sum_le_sum (fun j _ => uniqueFalseCircuit_size_le c _)
      _ = _ := by simp only [sum_const, card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]; ring
  omega

end AC0Circuit

lemma sampledAndPolynomial_error_detected {n k s : ℕ}
    (sample : GateSamplingChoices k k s) (c : Fin k → AC0Circuit n)
    (x : BooleanCube n)
    (h : sampledAndPolynomial sample (fun i => (c i).indicator x) ≠
      (AC0Circuit.andGate c).indicator x) :
    (AC0Circuit.gateSamplingException sample c).eval x = true := by
  rw [AC0Circuit.gateSamplingException_eval]
  have hb : sampledAndPolynomial sample (fun i => if (c i).eval x then 1 else 0) ≠
      boolAndValue (fun i => (c i).eval x) := by
    simpa only [AC0Circuit.indicator, AC0Circuit.eval, decide_eq_true_eq, boolAndValue] using h
  refine ⟨?_, sampledAndPolynomial_failure sample _ hb⟩
  intro hall
  apply hb
  rw [sampledAndPolynomial_all_true sample _ hall]
  exact (ite_eq_left hall).symm

lemma gateSamplingException_pointwise_probability {n k : ℕ} (s : ℕ)
    (c : Fin k → AC0Circuit n) (x : BooleanCube n) :
    (gateSamplingLaw k k s).probability
      (fun sample => (AC0Circuit.gateSamplingException sample c).eval x = true) ≤
        (7 / 8 : ℝ) ^ s := by
  by_cases hall : ∀ i, (c i).eval x = true
  · have hz : (gateSamplingLaw k k s).probability
        (fun sample => (AC0Circuit.gateSamplingException sample c).eval x = true) = 0 := by
      have he (sample : GateSamplingChoices k k s) :
          ¬(AC0Circuit.gateSamplingException sample c).eval x = true := by
        intro h
        exact ((AC0Circuit.gateSamplingException_eval sample c x).mp h).1 hall
      unfold FiniteLaw.probability
      simp only [ite_eq_right (he _)]
      exact FiniteLaw.average_const (gateSamplingLaw k k s) 0
    rw [hz]
    positivity
  · have hnonempty : (falseCoordinates (fun i => (c i).eval x)).Nonempty := by
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      refine ⟨i, ?_⟩
      cases hb : (c i).eval x <;> simp_all [falseCoordinates]
    have hcard : (falseCoordinates (fun i => (c i).eval x)).card ≤ k := by
      exact (card_le_card (filter_subset _ _)).trans_eq (card_fin k)
    apply le_trans ((gateSamplingLaw k k s).probability_mono ?_)
      (gateSamplingLaw_failure k k s _ hnonempty hcard)
    intro sample hsample
    exact (AC0Circuit.gateSamplingException_eval sample c x).mp hsample |>.2

theorem exists_gateSamplingException_small {n k : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (s : ℕ) (c : Fin k → AC0Circuit n) :
    ∃ sample : GateSamplingChoices k k s,
      ν.probability (fun x => (AC0Circuit.gateSamplingException sample c).eval x = true) ≤
        (7 / 8 : ℝ) ^ s := by
  exact exists_choice_of_pointwise_failure (gateSamplingLaw k k s) ν _
    (gateSamplingException_pointwise_probability s c)

end TwoPointCorrelations

end OAI
