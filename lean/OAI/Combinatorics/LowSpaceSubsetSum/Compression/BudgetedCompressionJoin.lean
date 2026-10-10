import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionCallbacks
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionReader
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedParentRemaining
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedParentSpent
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorFlow
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.JoinUserMap

namespace OAI

/-! # Concrete compression joins with an execution watchdog

The input arrays are shared, snapshots copy only the right tournament, and
callbacks execute the bounded dictionary operations. The charge is independent
of the queried values and of the success event.
-/

namespace LowSpaceSubsetSum.BudgetedCompressionJoin

universe u
variable {n : ℕ} {τ : Type u}
open CompressionReader (State)

def reference (P t : ℤ) (B : ℕ) (right₁ right₂ : Array ℤ) {d₁ d₂ : ℕ}
    (report : ℤ → ℤ → τ → (τ × Bool) × ℕ) (fuel₁ fuel₂ control : ℕ)
    (s₁ : State P .direct right₁ d₁) (s₂ : State P (.complementary t) right₂ d₂) (a : τ) :=
  CountedStreamJoin.runAcc
    (CompressionReader.read P .direct right₁) (CompressionReader.scalarKey P .direct)
    (CompressionReader.read P (.complementary t) right₂)
    (CompressionReader.scalarKey P (.complementary t)) (fun _ => 1) report
    (CompressionReader.snapshot P (.complementary t) right₂)
    B fuel₁ fuel₂ control (StreamJoin.start s₁ s₂ a)

def run (I : Instance n) (P t : ℤ) (B : ℕ) (right₁ right₂ : Array ℤ) {d₁ d₂ : ℕ}
    (report : ℤ → ℤ → τ → (τ × Bool) × ℕ) (fuel₁ fuel₂ control : ℕ)
    (s₁ : State P .direct right₁ d₁) (s₂ : State P (.complementary t) right₂ d₂)
    (a : τ) (budget : ℕ) :=
  let charge := inputScale I ^ 4
  BudgetedJoinExecution.run charge charge charge charge charge B
    (CompressionReader.read P .direct right₁) (CompressionReader.scalarKey P .direct)
    (CompressionReader.read P (.complementary t) right₂)
    (CompressionReader.scalarKey P (.complementary t)) (fun _ => 1) report
    (CompressionReader.snapshot P (.complementary t) right₂)
    B fuel₁ fuel₂ control (StreamJoin.start s₁ s₂ a) budget

theorem reference_value (P t : ℤ) (B : ℕ) (right₁ right₂ : Array ℤ) {d₁ d₂ : ℕ}
    (report : ℤ → ℤ → τ → (τ × Bool) × ℕ) (fuel₁ fuel₂ control : ℕ)
    (s₁ : State P .direct right₁ d₁) (s₂ : State P (.complementary t) right₂ d₂) (a : τ) :
    (reference P t B right₁ right₂ report fuel₁ fuel₂ control s₁ s₂ a).1 =
      StreamJoin.stopped
        (fun s => (CompressionReader.read P .direct right₁ s).1) (fun x => x % P)
        (fun s => (CompressionReader.read P (.complementary t) right₂ s).1)
        (fun y => (t - y) % P) (fun x y a => (report x y a).1)
        B fuel₁ fuel₂ control s₁ s₂ a := by
  exact CountedStreamJoin.runAcc_value _ _ _ _ _ _ _
    (CompressionReader.snapshot_value P (.complementary t) right₂) _ _ _ _ _

theorem run_value (I : Instance n) (P t : ℤ) (B : ℕ)
    (right₁ right₂ : Array ℤ) {d₁ d₂ : ℕ}
    (report : ℤ → ℤ → τ → (τ × Bool) × ℕ) (fuel₁ fuel₂ control : ℕ)
    (s₁ : State P .direct right₁ d₁) (s₂ : State P (.complementary t) right₂ d₂)
    (a : τ) (budget : ℕ) (out : StreamJoin.StoppedResult _ _ τ) (left : ℕ)
    (h : (run I P t B right₁ right₂ report fuel₁ fuel₂ control s₁ s₂ a budget).1 = some (out, left)) :
    out = (reference P t B right₁ right₂ report fuel₁ fuel₂ control s₁ s₂ a).1 ∧ left ≤ budget :=
  BudgetedJoinExecution.run_value _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem operation_charge {u : ℕ} (hu : 10000 ≤ u) : 2 * u ^ 2 + 32 ≤ u ^ 4 := by
  have h1 : 1 ≤ u ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsq : 34 ≤ u ^ 2 := by nlinarith only [hu]
  calc
    _ ≤ 34 * u ^ 2 := by omega
    _ ≤ u ^ 2 * u ^ 2 := Nat.mul_le_mul_right _ hsq
    _ = _ := by ring

theorem run_work (I : Instance n) (P t : ℤ) (B : ℕ)
    (right₁ right₂ : Array ℤ) {d₁ d₂ : ℕ}
    (report : ℤ → ℤ → τ → (τ × Bool) × ℕ) (fuel₁ fuel₂ control : ℕ)
    (s₁ : State P .direct right₁ d₁) (s₂ : State P (.complementary t) right₂ d₂)
    (a : τ) (budget : ℕ) (hn : 10000 ≤ n) (hd₁ : d₁ ≤ n) (hd₂ : d₂ ≤ n)
    (hreport : ∀ x y a, (report x y a).2 ≤ inputScale I ^ 2)
    (hcopy : 10 * 2 ^ (d₂ + 1) ≤ B) :
    (run I P t B right₁ right₂ report fuel₁ fuel₂ control s₁ s₂ a budget).2 ≤ budget + 1 := by
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hb := operation_charge hu
  have hsq : 4 ≤ inputScale I ^ 2 := by nlinarith only [hu]
  have hm : max (inputScale I ^ 2) 4 = inputScale I ^ 2 := max_eq_left hsq
  exact BudgetedJoinExecution.run_work
    (CompressionReader.read P .direct right₁) (CompressionReader.scalarKey P .direct)
    (CompressionReader.read P (.complementary t) right₂)
    (CompressionReader.scalarKey P (.complementary t)) (fun _ => 1) report
    (CompressionReader.snapshot P (.complementary t) right₂)
    (inputScale I ^ 2) 3 (inputScale I ^ 2) 3 1 (inputScale I ^ 2)
    (inputScale I ^ 4) (inputScale I ^ 4) (inputScale I ^ 4) (inputScale I ^ 4) (inputScale I ^ 4) B
    (fun s => CompressionReader.read_scale I hn P .direct right₁ s hd₁)
    (CompressionReader.scalarKey_work P .direct)
    (fun s => CompressionReader.read_scale I hn P (.complementary t) right₂ s hd₂)
    (CompressionReader.scalarKey_work P (.complementary t))
    (fun _ => le_rfl) hreport (by omega) (by omega) (by omega) (by omega)
    (by rw [hm]; omega)
    (fun s => (CompressionReader.snapshot_work P (.complementary t) right₂ s).trans hcopy)
    B fuel₁ fuel₂ control (StreamJoin.start s₁ s₂ a) budget

theorem query_charge (I : Instance n) (hn : 10000 ≤ n) :
    7 * inputScale I ^ 4 + 16 ≤ inputScale I ^ 5 := by
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have h1 : 1 ≤ inputScale I ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hs : 23 * inputScale I ^ 4 ≤ inputScale I ^ 5 := by
    calc
      _ ≤ inputScale I * inputScale I ^ 4 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' (inputScale I) 4).symm
  omega

theorem account (I : Instance n) (P t : ℤ) (B : ℕ)
    (right₁ right₂ : Array ℤ) {d₁ d₂ : ℕ}
    (report : ℤ → ℤ → τ → (τ × Bool) × ℕ) (fuel₁ fuel₂ control : ℕ)
    (s₁ : State P .direct right₁ d₁) (s₂ : State P (.complementary t) right₂ d₂)
    (a : τ) (budget : ℕ) (hn : 10000 ≤ n) (hd₁ : d₁ ≤ n) (hd₂ : d₂ ≤ n)
    (hreport : ∀ x y a, (report x y a).2 ≤ inputScale I ^ 2)
    (hcopy : 10 * 2 ^ (d₂ + 1) ≤ B) :
    BudgetedSeparatorFlow.Account budget
      (run I P t B right₁ right₂ report fuel₁ fuel₂ control s₁ s₂ a budget) := by
  refine ⟨run_work I P t B right₁ right₂ report fuel₁ fuel₂ control s₁ s₂ a budget
    hn hd₁ hd₂ hreport hcopy, ?_⟩
  intro out left h
  refine ⟨(run_value I P t B right₁ right₂ report fuel₁ fuel₂ control s₁ s₂ a budget out left h).2, ?_⟩
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hb := operation_charge hu
  have hsq : 4 ≤ inputScale I ^ 2 := by nlinarith only [hu]
  have hm : max (inputScale I ^ 2) 4 = inputScale I ^ 2 := max_eq_left hsq
  exact BudgetedJoinExecution.run_spent
    (CompressionReader.read P .direct right₁) (CompressionReader.scalarKey P .direct)
    (CompressionReader.read P (.complementary t) right₂)
    (CompressionReader.scalarKey P (.complementary t)) (fun _ => 1) report
    (CompressionReader.snapshot P (.complementary t) right₂)
    (inputScale I ^ 2) 3 (inputScale I ^ 2) 3 1 (inputScale I ^ 2)
    (inputScale I ^ 4) (inputScale I ^ 4) (inputScale I ^ 4) (inputScale I ^ 4) (inputScale I ^ 4) B
    (fun s => CompressionReader.read_scale I hn P .direct right₁ s hd₁)
    (CompressionReader.scalarKey_work P .direct)
    (fun s => CompressionReader.read_scale I hn P (.complementary t) right₂ s hd₂)
    (CompressionReader.scalarKey_work P (.complementary t))
    (fun _ => le_rfl) hreport (by omega) (by omega) (by omega) (by omega)
    (by rw [hm]; omega)
    (fun s => (CompressionReader.snapshot_work P (.complementary t) right₂ s).trans hcopy)
    B fuel₁ fuel₂ control (StreamJoin.start s₁ s₂ a) budget out left h

theorem run_complete (I : Instance n) (P t : ℤ) (B : ℕ)
    (right₁ right₂ : Array ℤ) {d₁ d₂ : ℕ}
    (report : ℤ → ℤ → τ → (τ × Bool) × ℕ) (fuel₁ fuel₂ control : ℕ)
    (s₁ : State P .direct right₁ d₁) (s₂ : State P (.complementary t) right₂ d₂)
    (a : τ) (budget : ℕ) (hn : 10000 ≤ n)
    (hb : let out := (reference P t B right₁ right₂ report fuel₁ fuel₂ control s₁ s₂ a).1
      inputScale I ^ 5 * out.state.queries + B * out.state.copies + 4 ≤ budget) :
    ∃ left, (run I P t B right₁ right₂ report fuel₁ fuel₂ control s₁ s₂ a budget).1 =
      some ((reference P t B right₁ right₂ report fuel₁ fuel₂ control s₁ s₂ a).1, left) := by
  apply BudgetedJoinExecution.run_complete_queries
  · exact CompressionReader.snapshot_value P (.complementary t) right₂
  · have hmul := Nat.mul_le_mul_right
      (reference P t B right₁ right₂ report fuel₁ fuel₂ control s₁ s₂ a).1.state.queries
      (query_charge I hn)
    change _ ≤ budget
    dsimp only at hb
    have he : 2 * inputScale I ^ 4 + inputScale I ^ 4 + inputScale I ^ 4 + inputScale I ^ 4 +
        2 * inputScale I ^ 4 + 16 = 7 * inputScale I ^ 4 + 16 := by omega
    rw [he]
    exact (Nat.add_le_add_right (Nat.add_le_add_right hmul _) _).trans hb

theorem run_remaining (I : Instance n) (P t : ℤ) (B : ℕ)
    (right₁ right₂ : Array ℤ) {d₁ d₂ : ℕ}
    (report : ℤ → ℤ → τ → (τ × Bool) × ℕ) (fuel₁ fuel₂ control : ℕ)
    (s₁ : State P .direct right₁ d₁) (s₂ : State P (.complementary t) right₂ d₂)
    (a : τ) (budget : ℕ) (hn : 10000 ≤ n) (out : StreamJoin.StoppedResult _ _ τ) (left : ℕ)
    (h : (run I P t B right₁ right₂ report fuel₁ fuel₂ control s₁ s₂ a budget).1 = some (out, left)) :
    budget ≤ left + inputScale I ^ 5 * out.state.queries + B * out.state.copies + 4 := by
  have hr := BudgetedJoinExecution.run_remaining_queries
    (inputScale I ^ 4) (inputScale I ^ 4) (inputScale I ^ 4) (inputScale I ^ 4) (inputScale I ^ 4) B
    (CompressionReader.read P .direct right₁) (CompressionReader.scalarKey P .direct)
    (CompressionReader.read P (.complementary t) right₂)
    (CompressionReader.scalarKey P (.complementary t)) (fun _ => 1) report
    (CompressionReader.snapshot P (.complementary t) right₂)
    (CompressionReader.snapshot_value P (.complementary t) right₂)
    B fuel₁ fuel₂ control s₁ s₂ a budget out left h
  have hmul := Nat.mul_le_mul_right out.state.queries (query_charge I hn)
  have he : 2 * inputScale I ^ 4 + inputScale I ^ 4 + inputScale I ^ 4 + inputScale I ^ 4 +
      2 * inputScale I ^ 4 + 16 = 7 * inputScale I ^ 4 + 16 := by omega
  rw [he] at hr
  omega

end LowSpaceSubsetSum.BudgetedCompressionJoin

end OAI
