import Mathlib.Algebra.Field.ZMod
import OAI.NumberTheory.Ostmann.Construction.TransferHistoryUniqueness
import OAI.NumberTheory.Ostmann.Characters.TreeCoordinates

namespace OAI

/-! # The actual integer pivot gives the spectator's rational reconstruction -/

namespace Ostmann

theorem ValidTransferNode.spectator_composite_reconstruction {State : Type*}
    {sys : TransferHistorySystem State} {σ : State} {s v w : ℤ} {P : ℕ}
    (h : ValidTransferNode sys σ s v w P) {q : ℕ} [Fact q.Prime]
    (u : (ZMod q)ˣ) (hs : (s : ZMod q) ≠ 0) :
    reconstructedEntry (s : ZMod q) (v : ZMod q) (w : ZMod q) u
      (sys.leftProduct σ : ZMod q) (sys.rightProduct σ : ZMod q) = (P : ZMod q) / u := by
  have hr : (v : ZMod q) * sys.rightProduct σ - (w : ZMod q) * sys.leftProduct σ =
      (s : ZMod q) * P := by
    have hz := congrArg (fun z : ℤ => (z : ZMod q)) h.relation
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using hz
  unfold reconstructedEntry
  rw [hr]
  field_simp

theorem ValidTransferNode.spectator_composite_zero_iff {State : Type*}
    {sys : TransferHistorySystem State} {σ : State} {s v w : ℤ} {P : ℕ}
    (h : ValidTransferNode sys σ s v w P) {q : ℕ} [Fact q.Prime]
    (u : (ZMod q)ˣ) (hs : (s : ZMod q) ≠ 0) :
    reconstructedEntry (s : ZMod q) (v : ZMod q) (w : ZMod q) u
      (sys.leftProduct σ : ZMod q) (sys.rightProduct σ : ZMod q) = 0 ↔ q ∣ P := by
  rw [h.spectator_composite_reconstruction u hs, div_eq_zero_iff,
    or_iff_left (Units.ne_zero u), ZMod.natCast_eq_zero_iff]

theorem spectator_frequency_ne_zero {q : ℕ} [Fact q.Prime] (s : ℤ)
    (hs : s ≠ 0) (hsmall : s.natAbs < q) : (s : ZMod q) ≠ 0 := by
  intro hz
  have hd : q ∣ s.natAbs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd s q).mp hz)
  exact (not_le_of_gt hsmall) (Nat.le_of_dvd (Int.natAbs_pos.mpr hs) hd)

theorem ValidTransferNode.spectator_reconstruction {State : Type*}
    {sys : TransferHistorySystem State} {σ : State} {s v w : ℤ} {P : ℕ}
    (h : ValidTransferNode sys σ s v w P) {q : ℕ} [Fact q.Prime]
    (u p : ℕ) (hP : P = u * p) (hs : (s : ZMod q) ≠ 0) (hu : (u : ZMod q) ≠ 0) :
    reconstructedEntry (s : ZMod q) (v : ZMod q) (w : ZMod q) (u : ZMod q)
      (sys.leftProduct σ : ZMod q) (sys.rightProduct σ : ZMod q) = (p : ZMod q) := by
  have hr : (v : ZMod q) * sys.rightProduct σ - (w : ZMod q) * sys.leftProduct σ =
      (s : ZMod q) * (u * p) := by
    have hi := h.relation
    rw [hP] at hi
    have hz := congrArg (fun z : ℤ => (z : ZMod q)) hi
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] using hz
  unfold reconstructedEntry
  apply (div_eq_iff (mul_ne_zero hs hu)).mpr
  rw [hr]
  ring

theorem ValidTransferNode.spectator_zero_iff {State : Type*}
    {sys : TransferHistorySystem State} {σ : State} {s v w : ℤ} {P : ℕ}
    (h : ValidTransferNode sys σ s v w P) {q : ℕ} [Fact q.Prime]
    (u p : ℕ) (hP : P = u * p) (hs : (s : ZMod q) ≠ 0) (hu : (u : ZMod q) ≠ 0) :
    reconstructedEntry (s : ZMod q) (v : ZMod q) (w : ZMod q) (u : ZMod q)
      (sys.leftProduct σ : ZMod q) (sys.rightProduct σ : ZMod q) = 0 ↔ q ∣ p := by
  rw [h.spectator_reconstruction u p hP hs hu, ZMod.natCast_eq_zero_iff]

theorem spectator_child_argument {q : ℕ} [Fact q.Prime] (s : ℤ) (D H : ZMod q)
    (u p P : ℕ) (hP : P = u * p) :
    childArgument (s : ZMod q) D (u : ZMod q) H (p : ZMod q) =
      (s : ZMod q) / (D * (P : ZMod q) * H) := by
  rw [hP, Nat.cast_mul]
  unfold childArgument
  congr 1
  ring

end Ostmann

end OAI
