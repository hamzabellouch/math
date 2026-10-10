import OAI.Combinatorics.BalancedRyser.Selection.SelectionState
import OAI.Combinatorics.BalancedRyser.Selection.SelectionTailCompletion

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I V : Type*} [Fintype I] [Fintype V]

def TailCheck (G : Input I V) (S : State I V) : Prop :=
  ∃ L Δ : ℕ, 3 ≤ L ∧
    (∀ i ∈ S.remaining, L ≤ (domain G S i).card) ∧
    (∀ v ∈ currentVertices G S, degree G S v ≤ Δ) ∧ 8 * Δ ≤ L

omit [Fintype I] in

theorem tailCheck_iff (G : Input I V) (S : State I V) :
    TailCheck G S ↔
      (∀ i ∈ S.remaining, 3 ≤ (domain G S i).card) ∧
      (∀ v ∈ currentVertices G S, ∀ i ∈ S.remaining,
        8 * degree G S v ≤ (domain G S i).card) := by
  constructor
  · rintro ⟨L, Δ, hL, hs, hd, hsp⟩
    exact ⟨fun i hi => hL.trans (hs i hi), fun v hv i hi =>
      (Nat.mul_le_mul_left 8 (hd v hv)).trans (hsp.trans (hs i hi))⟩
  · rintro ⟨hs, hd⟩
    let Δ := (currentVertices G S).sup (degree G S)
    refine ⟨max 3 (8 * Δ), Δ, le_max_left _ _, ?_, ?_, le_max_right _ _⟩
    · intro i hi
      apply max_le (hs i hi)
      have hdeg : Δ ≤ (domain G S i).card / 8 := by
        apply Finset.sup_le
        intro v hv
        exact (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa [Nat.mul_comm] using hd v hv i hi)
      exact (Nat.mul_le_mul_left 8 hdeg).trans (by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self (domain G S i).card 8)
    · intro v hv
      exact Finset.le_sup hv

def failureLaw (G : Input I V) : OutputLaw G where
  weight _ := 0
  nonnegative _ := le_rfl
  mass_le_one := by simp
  supported _ h := False.elim (lt_irrefl 0 h)

@[simp] theorem successMass_failureLaw (G : Input I V) :
    successMass (failureLaw G) = 0 := by simp [successMass, failureLaw]

section Nonempty
variable [Nonempty V]

def recordedAssignment (S : State I V) : I → V :=
  fun i => (S.recorded i).getD (Classical.choice inferInstance)

omit [Fintype I] [Fintype V] in
theorem recordedAssignment_recorded (G : Input I V) (S : State I V)
    (hS : StateInvariant G S) (i : I) (hi : i ∉ S.remaining) :
    S.recorded i = some (recordedAssignment S i) := by
  have hn : S.recorded i ≠ none := by
    intro h
    exact hi ((hS.2.1 i).mp h)
  cases hr : S.recorded i with
  | none => exact False.elim (hn hr)
  | some v => simp [recordedAssignment, hr]

def terminalLaw (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (S : State I V) : OutputLaw G := by
  classical
  letI : MeasurableSpace V := ⊤
  let : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  by_cases h : StateInvariant G S ∧ TailCheck G S
  · have hs : ∀ i ∉ S.remaining, G.slot (recordedAssignment S i) = i := by
      intro i hi
      exact h.1.2.2.1 i _ (recordedAssignment_recorded G S h.1 i hi)
    have hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
        ¬ G.graph.Adj (recordedAssignment S i) (recordedAssignment S j) := by
      intro i hi j hj hij
      exact h.1.2.2.2.1 i j _ _ (recordedAssignment_recorded G S h.1 i hi)
        (recordedAssignment_recorded G S h.1 j hj) hij
    have hc : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
        ¬ G.graph.Adj (recordedAssignment S i) v := by
      intro i hi v hv
      exact h.1.2.2.2.2 i _ (recordedAssignment_recorded G S h.1 i hi)
        v (Finset.mem_filter.mp hv).1
    have hne : (Tail.successfulAssignments G S).Nonempty := by
      obtain ⟨L, Δ, hL, hsize, hdegree, hsparse⟩ := h.2
      exact Tail.successfulAssignments_nonempty G S hno L Δ hL hsize hdegree hsparse
    exact Tail.completionOutputLaw G S (recordedAssignment S) hs hind hc hne
  · exact failureLaw G

theorem successMass_terminalLaw (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) (S : State I V) :
    successMass (terminalLaw G hno S) =
      if StateInvariant G S ∧ TailCheck G S then 1 else 0 := by
  unfold terminalLaw
  split
  · exact Tail.successMass_completionOutputLaw _ _ _ _ _ _ _
  · exact successMass_failureLaw G

def terminalOutcomeLaw (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) :
    Option (State I V) → OutputLaw G
  | none => failureLaw G
  | some S => terminalLaw G hno S

def SourceTailCheck (p : Parameters) (q : ℕ) (G : Input I V) (S : State I V) : Prop :=
  TailCheck G S ∧ ∀ i ∈ S.remaining,
    p.sizeScale q (p.lastMainTime q (Fintype.card I)) * p.c * q / 2 ≤
      ((domain G S i).card : ℝ)

def sourceTerminalLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (S : State I V) : OutputLaw G :=
  if SourceTailCheck p q G S then terminalLaw G hno S else failureLaw G

theorem successMass_sourceTerminalLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) (S : State I V) :
    successMass (sourceTerminalLaw p q G hno S) =
      if StateInvariant G S ∧ SourceTailCheck p q G S then 1 else 0 := by
  by_cases ht : SourceTailCheck p q G S
  · simp only [sourceTerminalLaw, ht, ite_true, successMass_terminalLaw]
    simp only [ht.1, and_true]
  · simp [sourceTerminalLaw, ht]

def sourceTerminalOutcomeLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) :
    Option (State I V) → OutputLaw G
  | none => failureLaw G
  | some S => sourceTerminalLaw p q G hno S

def finalLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) : OutputLaw G where
  weight a := ∑ out, mainStageWeight p q G out * (sourceTerminalOutcomeLaw p q G hno out).weight a
  nonnegative a := Finset.sum_nonneg (fun out _ =>
    mul_nonneg (historyWeight_nonnegative p q G _ out) ((sourceTerminalOutcomeLaw p q G hno out).nonnegative a))
  mass_le_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ out, mainStageWeight p q G out * 1 := Finset.sum_le_sum (fun out _ =>
        mul_le_mul_of_nonneg_left (sourceTerminalOutcomeLaw p q G hno out).mass_le_one
          (historyWeight_nonnegative p q G _ out))
      _ = 1 := by simp only [mul_one]; exact sum_historyWeight p q G _
  supported a ha := by
    by_contra hn
    have hz : ∀ out, (sourceTerminalOutcomeLaw p q G hno out).weight a = 0 :=
      fun out => weight_eq_zero_of_not_transversal (sourceTerminalOutcomeLaw p q G hno out) a hn
    simp only [hz, mul_zero, Finset.sum_const_zero, lt_self_iff_false] at ha

theorem successMass_finalLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) :
    successMass (finalLaw p q G hno) =
      ∑ S : State I V, if SourceTailCheck p q G S then mainStageWeight p q G (some S) else 0 := by
  have he : successMass (finalLaw p q G hno) =
      ∑ out, mainStageWeight p q G out * successMass (sourceTerminalOutcomeLaw p q G hno out) := by
    unfold successMass finalLaw
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
  rw [he, Fintype.sum_option]
  simp only [sourceTerminalOutcomeLaw, successMass_failureLaw, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro S _
  rw [successMass_sourceTerminalLaw]
  by_cases hS : StateInvariant G S
  · by_cases ht : SourceTailCheck p q G S <;> simp [hS, ht]
  · have hz : mainStageWeight p q G (some S) = 0 := by
      apply le_antisymm _ (historyWeight_nonnegative p q G _ _)
      by_contra hn
      exact hS (positive_historyWeight_invariant p q G _ S (lt_of_not_ge hn))
    simp [hS, hz]

theorem cylinderMass_finalLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (J : Finset I) (prescribed : I → V) :
    cylinderMass (finalLaw p q G hno) J prescribed =
      ∑ out, mainStageWeight p q G out *
        cylinderMass (sourceTerminalOutcomeLaw p q G hno out) J prescribed := by
  unfold cylinderMass finalLaw
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

theorem occupancyFailureMass_finalLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    {P D L : Type*} [Fintype P] [Fintype D] [Fintype L]
    (A : FiniteAffine.Plane q P D L) (line : V → L) (T : L → Finset P) (ρ : ℝ) :
    occupancyFailureMass (finalLaw p q G hno) A line T ρ =
      ∑ out, mainStageWeight p q G out *
        occupancyFailureMass (sourceTerminalOutcomeLaw p q G hno out) A line T ρ := by
  unfold occupancyFailureMass finalLaw
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

end Nonempty

theorem graphBounds_vertex_nonempty (G : Input I V) (q : ℕ) (c C : ℝ)
    (hc : 0 < c) (hq : 0 < q) (hG : GraphBounds G q c C) : Nonempty V := by
  have hi : 0 < Fintype.card I := by rw [hG.1]; omega
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp hi
  have hs : 0 < ((slotVertices G i).card : ℝ) :=
    (mul_pos hc (by exact_mod_cast hq)).trans_le (hG.2.2.1 i).1
  have hn : (slotVertices G i).Nonempty := Finset.card_pos.mp (by exact_mod_cast hs)
  obtain ⟨v, _⟩ := hn
  exact ⟨v⟩

def outputLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) : OutputLaw G :=
  if h : Nonempty V then @finalLaw I V _ _ h p q G hno else failureLaw G

@[simp] theorem outputLaw_eq_finalLaw [Nonempty V]
    (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) :
    outputLaw p q G hno = finalLaw p q G hno := by
  simp [outputLaw, show Nonempty V from inferInstance]

end
end Balanced.Selection.Process

end OAI
