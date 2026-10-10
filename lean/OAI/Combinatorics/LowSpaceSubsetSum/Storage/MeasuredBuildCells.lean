import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredInitialization
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredReaderCells

namespace OAI

/-! # Live cells during direct tournament initialization

The left subtree remains live while the right subtree is constructed. A
parent shares the completed children; it does not copy their payloads.
-/

namespace LowSpaceSubsetSum.MeasuredBuildCells

variable {α : Type*}

def run (N : ℕ) (key : α → (ℤ × ℕ) × ℕ) : (d : ℕ) →
    ((Fin d → Bool) → (Option α × ℕ) × ℕ) → (Tournament.Tree α d × ℕ) × ℕ
  | 0, front =>
    let x := front Fin.elim0
    ((.leaf x.1.1, x.1.2 + 1), x.2 + 2 * N + 8)
  | d + 1, front =>
    let l := run N key d (fun p => front (Fin.cons false p))
    let r := run N key d (fun p => front (Fin.cons true p))
    let w := MeasuredReaderCells.pick key (Tournament.winner l.1.1) (Tournament.winner r.1.1)
    let leftCells := N * (Tournament.nodes l.1.1 + 1)
    let bothCells := leftCells + N * (Tournament.nodes r.1.1 + 1)
    ((.node w.1.1 l.1.1 r.1.1, l.1.2 + r.1.2 + w.1.2 + 5),
      max (l.2 + 8) (max (leftCells + r.2 + 16) (bothCells + w.2 + N + 24)))

theorem run_value (N : ℕ) (key : α → (ℤ × ℕ) × ℕ) (d : ℕ)
    (front : (Fin d → Bool) → (Option α × ℕ) × ℕ) :
    (run N key d front).1 = Tournament.measuredBuild (fun x => (key x).1) d
      (fun p => (front p).1) := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [run, Tournament.measuredBuild, MeasuredReaderCells.pick_value, ih]

private theorem step_bound (N K R d l r w : ℕ)
    (hl : l ≤ (d + 1) * (4 * (N * 2 ^ (d + 1)) + K + R + 64))
    (hr : r ≤ (d + 1) * (4 * (N * 2 ^ (d + 1)) + K + R + 64))
    (hw : w ≤ K + 8) :
    max (l + 8) (max (N * 2 ^ (d + 1) + r + 16)
      (N * 2 ^ (d + 1) + N * 2 ^ (d + 1) + w + N + 24)) ≤
      (d + 2) * (4 * (N * 2 ^ (d + 2)) + K + R + 64) := by
  have hpow : 1 ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
  have hN : N ≤ N * 2 ^ (d + 1) := by nlinarith only [hpow]
  have hmul : N * 2 ^ (d + 2) = 2 * (N * 2 ^ (d + 1)) := by
    rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]
    ring
  have hcoeff : 4 * (N * 2 ^ (d + 1)) + K + R + 64 ≤
      4 * (N * 2 ^ (d + 2)) + K + R + 64 := by omega
  have hl' := hl.trans (Nat.mul_le_mul_left (d + 1) hcoeff)
  have hr' := hr.trans (Nat.mul_le_mul_left (d + 1) hcoeff)
  simp only [Nat.add_mul, Nat.one_mul] at hl' hr' ⊢
  omega

theorem run_cells (N : ℕ) (key : α → (ℤ × ℕ) × ℕ) (K R : ℕ)
    (hk : ∀ x, (key x).2 ≤ K) (d : ℕ)
    (front : (Fin d → Bool) → (Option α × ℕ) × ℕ) (hf : ∀ p, (front p).2 ≤ R) :
    (run N key d front).2 ≤ (d + 1) * (4 * (N * 2 ^ (d + 1)) + K + R + 64) := by
  induction d with
  | zero =>
    have h := hf Fin.elim0
    simp only [run, Nat.zero_add, pow_one, Nat.one_mul]
    omega
  | succ d ih =>
    have hl := ih (fun p => front (Fin.cons false p)) (fun p => hf _)
    have hr := ih (fun p => front (Fin.cons true p)) (fun p => hf _)
    have hw := MeasuredReaderCells.pick_cells key K hk
      (Tournament.winner (run N key d (fun p => front (Fin.cons false p))).1.1)
      (Tournament.winner (run N key d (fun p => front (Fin.cons true p))).1.1)
    simp only [run, Tournament.nodes_exact]
    exact step_bound N K R d _ _ _ hl hr hw

end LowSpaceSubsetSum.MeasuredBuildCells

end OAI
