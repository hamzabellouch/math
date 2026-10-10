import OAI.Combinatorics.EditApproximation.Coarse.CoarseReadAccess
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- Copy a range from an indexed immutable input. Each step charges the
source read, copied symbol bits, and literal binary address increment. -/


theorem coarseRangeCopyWithWork_value (read : ℕ → ℕ) (start length : ℕ) :
    (coarseRangeCopyWithWork read start length).1 =
      List.ofFn (fun i : Fin length => read (start + i.val)) := by
  induction length generalizing start with
  | zero => simp only [coarseRangeCopyWithWork, List.ofFn_zero]
  | succ length ih =>
    simp only [coarseRangeCopyWithWork, binaryNaturalAddWithWork_value, ih, List.ofFn_succ,
      Fin.val_zero, Nat.add_zero, Fin.val_succ, Nat.add_comm, Nat.add_left_comm]

theorem coarseRangeCopyWithWork_cost (read : ℕ → ℕ) (limit A S start length : ℕ)
    (hbits : ∀ i ≤ limit, Nat.size i ≤ A)
    (hsymbol : ∀ i < limit, Nat.size (read i) ≤ S) (hspan : start + length ≤ limit) :
    (coarseRangeCopyWithWork read start length).2 ≤ (length + 1) * (40 * (A + 1) + S) := by
  induction length generalizing start with
  | zero => simp only [coarseRangeCopyWithWork]; omega
  | succ length ih =>
    have hstart : start < limit := by omega
    have ha := hbits start (by omega)
    have hs := hsymbol start hstart
    have hc := binaryNaturalAddWithWork_cost start 1
    rw [show Nat.size 1 = 1 by decide] at hc
    have hr := ih (start + 1) (by omega)
    simp only [coarseRangeCopyWithWork, binaryNaturalAddWithWork_value]
    nlinarith only [ha, hs, hc, hr, Nat.zero_le A, Nat.zero_le S]

end EditApproximation

end OAI
