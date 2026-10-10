import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ScalarJoinCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionReaderCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionCallbackCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.BudgetedCompressionJoin

namespace OAI

/-! # Concrete compression join storage

The common scalar trace is instantiated with the actual tournament readers,
weight keys, snapshots and bounded trie callbacks. Shared input arrays are
retained by the surrounding pass and are not duplicated here.
-/

namespace LowSpaceSubsetSum.CompressionJoinCells

universe u
variable {n : ℕ} {τ : Type u}

def run (I : Instance n) (P t : ℤ) (B : ℕ) (right₁ right₂ : Array ℤ) {d₁ d₂ : ℕ}
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ) (userCells : τ → ℕ)
    (fuel₁ fuel₂ control : ℕ) (s₁ : CompressionReader.State P .direct right₁ d₁)
    (s₂ : CompressionReader.State P (.complementary t) right₂ d₂) (a : τ) (budget : ℕ) :=
  let charge := inputScale I^4
  ScalarJoinCells.run charge charge charge charge charge B
    (CompressionReaderCells.read P .direct right₁) (CompressionReaderCells.scalarKey P .direct)
    (CompressionReaderCells.read P (.complementary t) right₂)
    (CompressionReaderCells.scalarKey P (.complementary t)) report
    (CompressionReaderCells.snapshot P (.complementary t) right₂)
    CompressionReaderCells.stateCells CompressionReaderCells.stateCells userCells
    B fuel₁ fuel₂ control (StreamJoin.start s₁ s₂ a) budget

theorem value (I : Instance n) (P t : ℤ) (B : ℕ) (right₁ right₂ : Array ℤ) {d₁ d₂ : ℕ}
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ) (userCells : τ → ℕ)
    (fuel₁ fuel₂ control : ℕ) (s₁ : CompressionReader.State P .direct right₁ d₁)
    (s₂ : CompressionReader.State P (.complementary t) right₂ d₂) (a : τ) (budget : ℕ) :
    (run I P t B right₁ right₂ report userCells fuel₁ fuel₂ control s₁ s₂ a budget).1 =
      BudgetedCompressionJoin.run I P t B right₁ right₂ (fun x y a => (report x y a).1)
        fuel₁ fuel₂ control s₁ s₂ a budget := by
  rw [run,ScalarJoinCells.run_value]
  have hr₁ : (fun s : CompressionReader.State P .direct right₁ d₁ =>
      (CompressionReaderCells.read P .direct right₁ s).1) = CompressionReader.read P .direct right₁ :=
    funext (CompressionReaderCells.read_value P .direct right₁)
  have hr₂ : (fun s : CompressionReader.State P (.complementary t) right₂ d₂ =>
      (CompressionReaderCells.read P (.complementary t) right₂ s).1) =
      CompressionReader.read P (.complementary t) right₂ :=
    funext (CompressionReaderCells.read_value P (.complementary t) right₂)
  have hc : (fun s : CompressionReader.State P (.complementary t) right₂ d₂ =>
      (CompressionReaderCells.snapshot P (.complementary t) right₂ s).1) =
      CompressionReader.snapshot P (.complementary t) right₂ :=
    funext (CompressionReaderCells.snapshot_value P (.complementary t) right₂)
  rw [hr₁,hr₂,hc]
  rfl

private theorem large (I : Instance n) (hn : 10000 ≤ n) (C : ℕ) :
    128 ≤ inputScale I^4*(C+1) := by
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hp : inputScale I ≤ inputScale I^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ inputScale I by omega)
      (by decide : 1 ≤ 4)
  have hm : inputScale I^4 ≤ inputScale I^4*(C+1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem state_bound (I : Instance n) (hn : 10000 ≤ n) (C : ℕ)
    {P : ℤ} {mode : FilteredStream.Mode} {right : Array ℤ} {d : ℕ}
    (s : CompressionReader.State P mode right d) (ht : 2^(d+1) ≤ 4*(C+1)) :
    CompressionReaderCells.stateCells s ≤ inputScale I^4*(C+1) := by
  rw [CompressionReaderCells.stateCells_exact]
  have hp : 128 ≤ inputScale I^4 := by
    simpa only [Nat.zero_add,Nat.mul_one] using (large I hn 0)
  have hm := Nat.mul_le_mul_right (C+1) hp
  omega

theorem snapshot_bound (I : Instance n) (hn : 10000 ≤ n) (C : ℕ)
    (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) {d : ℕ}
    (s : CompressionReader.State P mode right d) (hd : d ≤ n) (ht : 2^(d+1) ≤ 4*(C+1)) :
    (CompressionReaderCells.snapshot P mode right s).2 ≤ inputScale I^4*(C+1) := by
  let u := inputScale I
  have hu : n+1 ≤ u := by unfold u inputScale; omega
  have hs := CompressionReaderCells.snapshot_cells P mode right s
  have ht' := Nat.mul_le_mul_left 20 ht
  have hsmall : (CompressionReaderCells.snapshot P mode right s).2 ≤ 104*u*(C+1) := by
    nlinarith only [hu,hd,hs,ht']
  have hp : 104*u ≤ u^4 := by
    have h1 : 1 ≤ u := by omega
    have hx : u ≤ u^3 := by simpa only [pow_one] using Nat.pow_le_pow_right h1 (by decide : 1 ≤ 3)
    have hc : 104 ≤ u^3 := by omega
    simpa only [pow_succ] using Nat.mul_le_mul_right u hc
  exact hsmall.trans (Nat.mul_le_mul_right (C+1) hp)

theorem cells (I : Instance n) (P t : ℤ) (B : ℕ) (right₁ right₂ : Array ℤ) {d₁ d₂ : ℕ}
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ) (userCells : τ → ℕ)
    (fuel₁ fuel₂ control : ℕ) (s₁ : CompressionReader.State P .direct right₁ d₁)
    (s₂ : CompressionReader.State P (.complementary t) right₂ d₂) (a : τ) (budget C : ℕ)
    (hn : 10000 ≤ n) (hd₁ : d₁ ≤ n) (hd₂ : d₂ ≤ n)
    (ht₁ : 2^(d₁+1) ≤ 4*(C+1)) (ht₂ : 2^(d₂+1) ≤ 4*(C+1)) (hB : B ≤ C)
    (hu : ∀ a, userCells a ≤ inputScale I^4*(C+1))
    (hr : ∀ x y a, (report x y a).2 ≤ inputScale I^4*(C+1)) :
    (run I P t B right₁ right₂ report userCells fuel₁ fuel₂ control s₁ s₂ a budget).2 ≤
      inputScale I^5*(C+1) := by
  let H := inputScale I^4*(C+1)
  have hH : 100 ≤ H := (by exact (show 100 ≤ 128 by decide).trans (large I hn C))
  have hk₁ : ∀ x, (CompressionReaderCells.scalarKey P .direct x).2 ≤ H := fun _ => by
    change 8 ≤ H; omega
  have hk₂ : ∀ x, (CompressionReaderCells.scalarKey P (.complementary t) x).2 ≤ H := fun _ => by
    change 8 ≤ H; omega
  have hC : C ≤ H := by
    have hp : 1 ≤ inputScale I^4 := Nat.one_le_pow _ _ (by unfold inputScale; omega)
    have hm := Nat.mul_le_mul_right (C+1) hp
    dsimp only [H]
    omega
  have h := ScalarJoinCells.run_cells
    (inputScale I^4) (inputScale I^4) (inputScale I^4) (inputScale I^4) (inputScale I^4) B
    (CompressionReaderCells.read P .direct right₁) (CompressionReaderCells.scalarKey P .direct)
    (CompressionReaderCells.read P (.complementary t) right₂)
    (CompressionReaderCells.scalarKey P (.complementary t)) report
    (CompressionReaderCells.snapshot P (.complementary t) right₂)
    CompressionReaderCells.stateCells CompressionReaderCells.stateCells userCells H hH
    (fun s => state_bound I hn C s ht₁) (fun s => state_bound I hn C s ht₂) hu
    (fun s => CompressionReaderCells.read_scale I hn P .direct right₁ s C hd₁ ht₁)
    (fun s => CompressionReaderCells.read_scale I hn P (.complementary t) right₂ s C hd₂ ht₂)
    hk₁ hk₂ hr (fun s => snapshot_bound I hn C P (.complementary t) right₂ s hd₂ ht₂)
    B fuel₁ fuel₂ control (hB.trans hC) (StreamJoin.start s₁ s₂ a) budget
  change (run I P t B right₁ right₂ report userCells fuel₁ fuel₂ control s₁ s₂ a budget).2 ≤ 65*H at h
  have hup : 65 ≤ inputScale I := by unfold inputScale; omega
  have hm : 65*H ≤ inputScale I^5*(C+1) := by
    calc
      _ ≤ inputScale I*H := Nat.mul_le_mul_right H hup
      _ = _ := by dsimp only [H]; rw [←Nat.mul_assoc,←pow_succ']
  exact h.trans hm

end LowSpaceSubsetSum.CompressionJoinCells

end OAI
