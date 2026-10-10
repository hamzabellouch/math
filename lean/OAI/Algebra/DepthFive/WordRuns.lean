import OAI.Algebra.DepthFive.WordSwitches

namespace OAI

/-! Counts of true runs, and their relation to adjacent switches. -/

open scoped BigOperators

namespace Problem335.WordRuns

/-- Number of transitions from false to true. -/
def riseCount {n : ℕ} (w : Fin (n + 1) → Bool) : ℕ :=
  ∑ i : Fin n, if w i.castSucc = false ∧ w i.succ = true then 1 else 0

/-- Number of transitions from true to false. -/
def fallCount {n : ℕ} (w : Fin (n + 1) → Bool) : ℕ :=
  ∑ i : Fin n, if w i.castSucc = true ∧ w i.succ = false then 1 else 0

/-- True runs are counted by their first letters. -/
def runCount {n : ℕ} (w : Fin (n + 1) → Bool) : ℕ :=
  riseCount w + (w 0).toNat

/-- In a mixed word, the number of true runs touching an endpoint. -/
def endpointRunCount {n : ℕ} (w : Fin (n + 1) → Bool) : ℕ :=
  (w 0).toNat + (w (Fin.last n)).toNat

/-- Number of true runs not touching an endpoint. -/
def interiorRunCount {n : ℕ} (w : Fin (n + 1) → Bool) : ℕ :=
  runCount w - endpointRunCount w

@[simp] theorem riseCount_cons {n : ℕ} (b : Bool) (w : Fin (n + 1) → Bool) :
    riseCount (Fin.cons b w) =
      (if b = false ∧ w 0 = true then 1 else 0) + riseCount w := by
  unfold riseCount
  rw [Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_succ]

@[simp] theorem fallCount_cons {n : ℕ} (b : Bool) (w : Fin (n + 1) → Bool) :
    fallCount (Fin.cons b w) =
      (if b = true ∧ w 0 = false then 1 else 0) + fallCount w := by
  unfold fallCount
  rw [Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_succ]

/-- Every switch is exactly a rise or a fall. -/
theorem switches_card_eq_rises_add_falls {n : ℕ} (w : Fin (n + 1) → Bool) :
    (WordSwitches.switches w).card = riseCount w + fallCount w := by
  rw [WordSwitches.switches, Finset.card_filter]
  unfold riseCount fallCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases w i.castSucc <;> cases w i.succ <;> decide

/-- Incoming and outgoing changes balance, up to the endpoint bits. -/
theorem rise_first_eq_fall_last {n : ℕ} (w : Fin (n + 1) → Bool) :
    riseCount w + (w 0).toNat = fallCount w + (w (Fin.last n)).toNat := by
  induction n with
  | zero => simp [riseCount, fallCount, Fin.last_zero]
  | succ n ih =>
    obtain ⟨⟨b, v⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 2) => Bool)).surjective w
    have hv := ih v
    have hb : (if b = false ∧ v 0 = true then 1 else 0) + b.toNat =
        (if b = true ∧ v 0 = false then 1 else 0) + (v 0).toNat := by
      cases b <;> cases v 0 <;> decide
    change riseCount (Fin.cons b v) + b.toNat =
      fallCount (Fin.cons b v) + (v (Fin.last n)).toNat
    rw [riseCount_cons, fallCount_cons]
    omega

/-- With no rises, a true last letter forces the entire word to be true. -/
theorem all_true_of_no_rises {n : ℕ} (w : Fin (n + 1) → Bool)
    (h : riseCount w = 0) (hlast : w (Fin.last n) = true) :
    ∀ i, w i = true := by
  induction n with
  | zero =>
    intro i
    have hi : i = Fin.last 0 := Fin.eq_zero i
    simpa [hi] using hlast
  | succ n ih =>
    obtain ⟨⟨b, v⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 2) => Bool)).surjective w
    change riseCount (Fin.cons b v) = 0 at h
    rw [riseCount_cons] at h
    change v (Fin.last n) = true at hlast
    have hv0 : riseCount v = 0 := by omega
    have hv := ih v hv0 hlast
    have hb : b = true := by
      have hvhead := hv 0
      cases b <;> simp_all
    intro i
    cases i using Fin.cases <;> simp [Fin.consEquiv_apply, hb, hv]

/-- If there is a false letter, each true endpoint belongs to a distinct run. -/
theorem endpointRunCount_le_runCount {n : ℕ} (w : Fin (n + 1) → Bool)
    (hfalse : ∃ i, w i = false) : endpointRunCount w ≤ runCount w := by
  unfold endpointRunCount runCount
  have hlast : (w (Fin.last n)).toNat ≤ riseCount w := by
    cases hl : w (Fin.last n) with
    | false => simp
    | true =>
      simp only [Bool.toNat_true]
      by_contra hnot
      have hz : riseCount w = 0 := by omega
      obtain ⟨i, hi⟩ := hfalse
      have ht := all_true_of_no_rises w hz hl i
      simp [hi] at ht
  omega

theorem endpointRunCount_le_two {n : ℕ} (w : Fin (n + 1) → Bool) :
    endpointRunCount w ≤ 2 := by
  unfold endpointRunCount
  cases w 0 <;> cases w (Fin.last n) <;> decide

/-- For a mixed word, switches equal twice the interior true runs plus endpoint runs.
In fact only the existence of a false letter is needed. -/
theorem switches_card_eq_two_interior_add_endpoint {n : ℕ}
    (w : Fin (n + 1) → Bool) (hfalse : ∃ i, w i = false) :
    (WordSwitches.switches w).card =
      2 * interiorRunCount w + endpointRunCount w := by
  have he := endpointRunCount_le_runCount w hfalse
  have hb := rise_first_eq_fall_last w
  rw [switches_card_eq_rises_add_falls]
  unfold interiorRunCount runCount endpointRunCount at *
  omega

/-- A version valid even for the all-true word: each run has two boundary ends,
except that endpoints do not contribute switches. -/
theorem two_runCount_eq_switches_add_endpoint {n : ℕ}
    (w : Fin (n + 1) → Bool) :
    2 * runCount w = (WordSwitches.switches w).card + endpointRunCount w := by
  have hb := rise_first_eq_fall_last w
  rw [switches_card_eq_rises_add_falls]
  unfold runCount endpointRunCount
  omega

end Problem335.WordRuns

end OAI
