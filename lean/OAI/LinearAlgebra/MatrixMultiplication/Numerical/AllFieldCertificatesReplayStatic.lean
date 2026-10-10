import OAI.LinearAlgebra.MatrixMultiplication.Numerical.AllFieldCertificatesReplay

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

namespace MatrixMultiplication.AllFieldCertificates.Replay

def Op.before (n : ℕ) : Op → Bool
  | .constant _ => true
  | .add i j => decide (i < n ∧ j < n)
  | .neg i => decide (i < n)
  | .mul i j => decide (i < n ∧ j < n)
  | .inv i => decide (i < n)
  | .log i => decide (i < n)

def checkOp (two : Ball) (v : ℕ → Ball) (op : Op) (w : Witness) : Bool :=
  match op with
  | .constant q => contains (.exact q) w.ball
  | .add i j => contains (Ball.add (v i) (v j)) w.ball
  | .neg i => contains (Ball.neg (v i)) w.ball
  | .mul i j => contains (Ball.mul (v i) (v j)) w.ball
  | .inv i => decide (0 < (v i).lower) && contains (Ball.inv (v i)) w.ball
  | .log i => match w.logarithm with
    | none => false
    | some lw => checkLog two (v i) w.ball lw

theorem checkOp_sound {two : Ball} (htwo : two.Encloses (Real.log 2))
    {bs : ℕ → Ball} {vs : ℕ → ℝ} {n : ℕ}
    (hr : ∀ i < n, (bs i).Encloses (vs i))
    {op : Op} {w : Witness} (hw : op.before n = true)
    (hc : checkOp two bs op w = true) : w.ball.Encloses (op.value vs) := by
  cases op with
  | constant q => exact contains_sound (Ball.exact_sound q) hc
  | add i j =>
      have h : i < n ∧ j < n := of_decide_eq_true hw
      exact contains_sound (Ball.add_sound (hr i h.1) (hr j h.2)) hc
  | neg i =>
      exact contains_sound (Ball.neg_sound (hr i (of_decide_eq_true hw))) hc
  | mul i j =>
      have h : i < n ∧ j < n := of_decide_eq_true hw
      exact contains_sound (Ball.mul_sound (hr i h.1) (hr j h.2)) hc
  | inv i =>
      simp only [checkOp, Bool.and_eq_true] at hc
      exact contains_sound
        (Ball.inv_sound (hr i (of_decide_eq_true hw)) (of_decide_eq_true hc.1)) hc.2
  | log i =>
      cases hl : w.logarithm with
      | none => simp [checkOp, hl] at hc
      | some lw =>
          simp only [checkOp, hl] at hc
          exact checkLog_sound htwo (hr i (of_decide_eq_true hw)) hc

def checkAt (two : Ball) (ops : ℕ → Op) (bs : ℕ → Ball) (i : ℕ) (w : Witness) : Bool :=
  decide (w.ball = bs i) && (ops i).before i && checkOp two bs (ops i) w

def checkRange (two : Ball) (ops : ℕ → Op) (bs : ℕ → Ball) : ℕ → List Witness → Bool
  | _, [] => true
  | start, w :: ws =>
      checkAt two ops bs start w && checkRange two ops bs (start + 1) ws

theorem checkRange_at {two : Ball} {ops : ℕ → Op} {bs : ℕ → Ball}
    (ws : List Witness) (start : ℕ)
    (hc : checkRange two ops bs start ws = true) (j : ℕ) (hj : j < ws.length) :
    ∃ w, checkAt two ops bs (start + j) w = true := by
  induction ws generalizing start j with
  | nil => simp at hj
  | cons w ws ih =>
      simp only [checkRange, Bool.and_eq_true] at hc
      cases j with
      | zero => exact ⟨w, by simpa using hc.1⟩
      | succ j =>
          obtain ⟨v, hv⟩ := ih (start + 1) hc.2 j (by simpa using hj)
          refine ⟨v, ?_⟩
          have hi : start + Nat.succ j = start + 1 + j := by omega
          rw [hi]
          exact hv

theorem checkRange_append (two : Ball) (ops : ℕ → Op) (bs : ℕ → Ball)
    (as cs : List Witness) (start : ℕ) :
    checkRange two ops bs start (as ++ cs) =
      (checkRange two ops bs start as && checkRange two ops bs (start + as.length) cs) := by
  induction as generalizing start with
  | nil => simp [checkRange]
  | cons a as ih =>
      simp only [List.cons_append, checkRange, List.length_cons]
      rw [ih]
      have hi : start + 1 + as.length = start + (as.length + 1) := by omega
      rw [hi]
      exact (Bool.and_assoc _ _ _).symm

theorem checkedValues_sound {two : Ball} (htwo : two.Encloses (Real.log 2))
    (ops : ℕ → Op) (bs : ℕ → Ball) (vs : ℕ → ℝ) (count : ℕ)
    (heval : ∀ i < count, vs i = (ops i).value vs)
    (hc : ∀ i < count, ∃ w, checkAt two ops bs i w = true) :
    ∀ i < count, (bs i).Encloses (vs i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi
      obtain ⟨w, hw⟩ := hc i hi
      simp only [checkAt, Bool.and_eq_true] at hw
      have hb : w.ball = bs i := of_decide_eq_true hw.1.1
      rw [heval i hi, ← hb]
      apply checkOp_sound htwo (n := i) _ hw.1.2 hw.2
      intro j hj
      exact ih j hj (hj.trans hi)

def RangeChecked (two : Ball) (ops : ℕ → Op) (bs : ℕ → Ball) (lo hi : ℕ) : Prop :=
  ∀ i, lo ≤ i → i < hi → ∃ w, checkAt two ops bs i w = true

theorem rangeChecked_of_checkRange {two : Ball} {ops : ℕ → Op} {bs : ℕ → Ball}
    (ws : List Witness) (start : ℕ)
    (hc : checkRange two ops bs start ws = true) :
    RangeChecked two ops bs start (start + ws.length) := by
  intro i hlo hhi
  have h := checkRange_at ws start hc (i - start) (by omega)
  simpa only [Nat.add_sub_of_le hlo] using h

theorem RangeChecked.join {two : Ball} {ops : ℕ → Op} {bs : ℕ → Ball}
    {lo mid hi : ℕ} (hl : RangeChecked two ops bs lo mid)
    (hr : RangeChecked two ops bs mid hi) : RangeChecked two ops bs lo hi := by
  intro i hlo hhi
  by_cases hm : i < mid
  · exact hl i hlo hm
  · exact hr i (Nat.le_of_not_gt hm) hhi

end MatrixMultiplication.AllFieldCertificates.Replay

end OAI
