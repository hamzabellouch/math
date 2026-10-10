import OAI.Dynamics.ConditionalShuffle.ScheduledRate

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Scheduled
open Thorp Thorp.Conditional Thorp.Conditional.Hybrid Revealed.Instrument

lemma chunks_const_apply {S : Type} (t : ℕ) (ht : 0 < t) (q : Fin t → S) (n : ℕ)
    (i : Fin (t*n)) : chunks S t n (fun _ => q) i = q ⟨i.val % t, Nat.mod_lt _ ht⟩ := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      have hh : (fun _ : Fin (n+1) => q) = Fin.snoc (fun _ : Fin n => q) q := by
        funext j; refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
      rw [hh, chunks_snoc]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left, ih]
        rfl
      · erw [Fin.append_right]
        congr 1
        apply Fin.ext
        simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]

lemma append_false (a b : ℕ) :
    Fin.append (fun _ : Fin a => false) (fun _ : Fin b => false) = fun _ => false := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

lemma append_false_true (a b : ℕ) (i : Fin (a+b)) :
    Fin.append (fun _ : Fin a => false) (fun _ : Fin b => true) i = decide (a ≤ i.val) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left, Fin.val_castAdd]
    exact (decide_eq_false (Nat.not_le.mpr j.isLt)).symm
  · simp only [Fin.append_right, Fin.val_natAdd]
    exact (decide_eq_true (Nat.le_add_right a j.val)).symm

lemma cycleSchedule_apply (g : ℕ) (i : Fin (periodLength g)) :
    cycleSchedule g i = decide (209*(g+3) ≤ i.val) := by
  unfold cycleSchedule
  rw [append_false]
  erw [append_false_true]
  exact congrArg (fun x : ℕ => decide (x ≤ i.val))
    (show 9*(g+3)+200*(g+3) = 209*(g+3) by omega)

def selectedSchedule (g s : ℕ) : Bool := decide (209*(g+3) ≤ s % periodLength g)

lemma periodLength_pos (g : ℕ) : 0 < periodLength g := by rw [periodLength_eq]; omega

lemma selected_periodic (g k s : ℕ) :
    selectedSchedule g (segmentLength g*k+s) = selectedSchedule g s := by
  unfold selectedSchedule segmentLength
  congr 1
  rw [Nat.add_mod, Nat.mul_assoc, Nat.mul_mod_right, zero_add, Nat.mod_mod]

lemma selected_segment (g : ℕ) (i : Fin (segmentLength g)) :
    selectedSchedule g i.val = segmentSchedule g i.val := by
  conv_rhs => rw [segmentSchedule, dite_eq_left i.isLt]
  change _ = chunks Bool (periodLength g) 800 (fun _ => cycleSchedule g) i
  erw [chunks_const_apply _ (periodLength_pos g), cycleSchedule_apply]
  rfl

lemma selected_active (g s : ℕ) (h : selectedSchedule g s = true) :
    Overlay.isActive (g+3) s = true := by
  unfold selectedSchedule at h
  have hh : 209*(g+3) ≤ s % periodLength g := of_decide_eq_true h
  have hl : s % periodLength g < 210*(g+3) := by
    rw [← periodLength_eq]; exact Nat.mod_lt _ (periodLength_pos g)
  unfold Overlay.isActive
  apply decide_eq_true
  have hd : 21*(g+3) ∣ periodLength g := by
    rw [periodLength_eq]; exact ⟨10, by omega⟩
  rw [← Nat.mod_mod_of_dvd s hd]
  have he : s % periodLength g = 189*(g+3) + (s % periodLength g - 189*(g+3)) := by omega
  rw [he, Nat.add_mod]
  have hz : 189*(g+3) % (21*(g+3)) = 0 := Nat.mod_eq_zero_of_dvd ⟨9, by omega⟩
  rw [hz, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  omega

end Revealed.Scheduled

end

end OAI
