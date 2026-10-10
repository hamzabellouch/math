import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionContext
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.BudgetedCompressionJoin

namespace OAI

/-! # One compression residue pass on retained reader contexts

The left bounded dictionary remains live during the right join. Overflow
skips that join. The shared budget is decreased by the executed joins; no
reference run is evaluated to choose the watchdog.
-/

namespace LowSpaceSubsetSum.BudgetedCompressionPass

open BudgetedSeparatorFlow
open CompressionContext (Context)

variable {n : ℕ} {P t z : ℤ}

structure Data (P t z : ℤ) where
  first : Context P .direct
  second : Context P (.complementary z)
  third : Context P .direct
  fourth : Context P (.complementary (t - z))
  fuel₀ : ℕ
  fuel₁ : ℕ
  fuel₂ : ℕ
  fuel₃ : ℕ

def leftFull (I : Instance n) (C B : ℕ) (D : Data P t z) :=
  BudgetedCompressionJoin.reference P z B D.first.right D.second.right
    (CompressionCallbacks.report I C) D.fuel₀ D.fuel₁ (D.fuel₀ + D.fuel₁ + 1)
    D.first.state D.second.state (CompressionCallbacks.empty I C)

def rightFull (I : Instance n) (B : ℕ) (D : Data P t z) (tree : BinaryTrie.Tree) :=
  BudgetedCompressionJoin.reference P (t - z) B D.third.right D.fourth.right
    (CompressionCallbacks.probe I tree t) D.fuel₂ D.fuel₃ (D.fuel₂ + D.fuel₃ + 1)
    D.third.state D.fourth.state false

def reference (I : Instance n) (C B : ℕ) (D : Data P t z) : Bool :=
  let left := (leftFull I C B D).1.state.user.val.keys
  if left.overflow then false else (rightFull I B D left.tree).1.state.user

def left (I : Instance n) (C B : ℕ) (D : Data P t z) (budget : ℕ) :=
  BudgetedCompressionJoin.run I P z B D.first.right D.second.right
    (CompressionCallbacks.report I C) D.fuel₀ D.fuel₁ (D.fuel₀ + D.fuel₁ + 1)
    D.first.state D.second.state (CompressionCallbacks.empty I C) budget

def right (I : Instance n) (B : ℕ) (D : Data P t z) (tree : BinaryTrie.Tree) (budget : ℕ) :=
  BudgetedCompressionJoin.run I P (t - z) B D.third.right D.fourth.right
    (CompressionCallbacks.probe I tree t) D.fuel₂ D.fuel₃ (D.fuel₂ + D.fuel₃ + 1)
    D.third.state D.fourth.state false budget

def run (I : Instance n) (C B : ℕ) (D : Data P t z) (budget : ℕ) :=
  bind (BudgetedSeparatorCall.run 8 (fun _ => ((), 7)) budget) fun _ rest =>
    bind (left I C B D rest) fun l available =>
      if l.state.user.val.keys.overflow then pure false available
      else bind (right I B D l.state.user.val.keys.tree available) fun r remaining =>
        pure r.state.user remaining

theorem value (I : Instance n) (C B : ℕ) (D : Data P t z)
    (budget : ℕ) (v : Bool) (remaining : ℕ)
    (h : (run I C B D budget).1 = some (v, remaining)) :
    v = reference I C B D ∧ remaining ≤ budget := by
  obtain ⟨tag, first, hf, hnext⟩ := (bind_eq_some _ _ _ _).mp h
  obtain ⟨_, hfirst, _⟩ := BudgetedSeparatorCall.value _ _ _ _ _ hf
  obtain ⟨l, available, hl, hr⟩ := (bind_eq_some _ _ _ _).mp hnext
  have hlv := BudgetedCompressionJoin.run_value I P z B D.first.right D.second.right
    (CompressionCallbacks.report I C) D.fuel₀ D.fuel₁ (D.fuel₀ + D.fuel₁ + 1)
    D.first.state D.second.state (CompressionCallbacks.empty I C) first l available hl
  change l = (leftFull I C B D).1 ∧ available ≤ first at hlv
  unfold reference
  rw [← hlv.1]
  split at hr
  next ho =>
    simp only [BudgetedSeparatorFlow.pure, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact ⟨by rw [ite_eq_left ho], by omega⟩
  next ho =>
    obtain ⟨r, rest, hr, hp⟩ := (bind_eq_some _ _ _ _).mp hr
    have hrv := BudgetedCompressionJoin.run_value I P (t - z) B D.third.right D.fourth.right
      (CompressionCallbacks.probe I l.state.user.val.keys.tree t)
      D.fuel₂ D.fuel₃ (D.fuel₂ + D.fuel₃ + 1) D.third.state D.fourth.state false
      available r rest hr
    change r = (rightFull I B D l.state.user.val.keys.tree).1 ∧ rest ≤ available at hrv
    simp only [BudgetedSeparatorFlow.pure, Option.some.injEq, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩
    exact ⟨by rw [ite_eq_right ho, hrv.1], by omega⟩

theorem account (I : Instance n) (C B : ℕ) (D : Data P t z) (budget : ℕ)
    (hn : 10000 ≤ n)
    (h₀ : D.first.depth ≤ n) (h₁ : D.second.depth ≤ n)
    (h₂ : D.third.depth ≤ n) (h₃ : D.fourth.depth ≤ n)
    (hc₁ : 10 * 2 ^ (D.second.depth + 1) ≤ B)
    (hc₃ : 10 * 2 ^ (D.fourth.depth + 1) ≤ B) :
    Account budget (run I C B D budget) := by
  apply bind_account
  · exact ⟨BudgetedSeparatorCall.work _ _ _ (by decide),
      fun v remaining h => BudgetedSeparatorCall.spent _ _ _ (by decide) v remaining h⟩
  · intro tag first hf
    apply bind_account
    · exact BudgetedCompressionJoin.account I P z B D.first.right D.second.right
        (CompressionCallbacks.report I C) D.fuel₀ D.fuel₁ (D.fuel₀ + D.fuel₁ + 1)
        D.first.state D.second.state (CompressionCallbacks.empty I C) first
        hn h₀ h₁ (CompressionCallbacks.report_scale I hn C) hc₁
    · intro l available hl
      split
      · exact pure_account false available
      · apply bind_account
        · exact BudgetedCompressionJoin.account I P (t - z) B D.third.right D.fourth.right
            (CompressionCallbacks.probe I l.state.user.val.keys.tree t)
            D.fuel₂ D.fuel₃ (D.fuel₂ + D.fuel₃ + 1) D.third.state D.fourth.state false
            available hn h₂ h₃ (CompressionCallbacks.probe_scale I hn _ t) hc₃
        · intro r remaining hr
          exact pure_account r.state.user remaining

def leftBill (I : Instance n) (C B : ℕ) (D : Data P t z) : ℕ :=
  let out := (leftFull I C B D).1.state
  inputScale I ^ 5 * out.queries + B * out.copies + 4

def rightBill (I : Instance n) (B : ℕ) (D : Data P t z) (tree : BinaryTrie.Tree) : ℕ :=
  let out := (rightFull I B D tree).1.state
  inputScale I ^ 5 * out.queries + B * out.copies + 4

def allowance (I : Instance n) (C B : ℕ) (D : Data P t z) : ℕ :=
  let l := (leftFull I C B D).1.state.user.val.keys
  8 + leftBill I C B D + if l.overflow then 0 else rightBill I B D l.tree

theorem complete (I : Instance n) (C B : ℕ) (D : Data P t z) (hn : 10000 ≤ n)
    (budget : ℕ) (hb : allowance I C B D ≤ budget) :
    ∃ v remaining, (run I C B D budget).1 = some (v, remaining) := by
  have hhead : 8 ≤ budget := by dsimp only [allowance] at hb; omega
  have hleft : leftBill I C B D ≤ budget - 8 := by dsimp only [allowance] at hb; omega
  obtain ⟨available, hl⟩ := BudgetedCompressionJoin.run_complete I P z B
    D.first.right D.second.right (CompressionCallbacks.report I C)
    D.fuel₀ D.fuel₁ (D.fuel₀ + D.fuel₁ + 1) D.first.state D.second.state
    (CompressionCallbacks.empty I C) (budget - 8) hn hleft
  have hrem := BudgetedCompressionJoin.run_remaining I P z B D.first.right D.second.right
    (CompressionCallbacks.report I C) D.fuel₀ D.fuel₁ (D.fuel₀ + D.fuel₁ + 1)
    D.first.state D.second.state (CompressionCallbacks.empty I C)
    (budget - 8) hn (leftFull I C B D).1 available hl
  have hrem' : budget - 8 ≤ available + leftBill I C B D := by
    simpa only [leftBill, Nat.add_assoc] using hrem
  have hh := congrArg Prod.fst (BudgetedSeparatorCall.complete 8 (fun _ => ((), 7)) budget hhead)
  unfold run left
  simp only [BudgetedSeparatorFlow.bind, hh, hl]
  split
  · exact ⟨false, available, rfl⟩
  · have hright : rightBill I B D (leftFull I C B D).1.state.user.val.keys.tree ≤ available := by
      dsimp only [allowance] at hb
      split at hb
      · contradiction
      · omega
    obtain ⟨remaining, hr⟩ := BudgetedCompressionJoin.run_complete I P (t - z) B
      D.third.right D.fourth.right
      (CompressionCallbacks.probe I (leftFull I C B D).1.state.user.val.keys.tree t)
      D.fuel₂ D.fuel₃ (D.fuel₂ + D.fuel₃ + 1) D.third.state D.fourth.state false
      available hn hright
    dsimp only [leftFull] at hr
    refine ⟨(rightFull I B D (leftFull I C B D).1.state.user.val.keys.tree).1.state.user,
      remaining, ?_⟩
    simp only [right, hr, BudgetedSeparatorFlow.pure]
    rfl

theorem remaining (I : Instance n) (C B : ℕ) (D : Data P t z) (hn : 10000 ≤ n)
    (budget : ℕ) (v : Bool) (rest : ℕ)
    (h : (run I C B D budget).1 = some (v, rest)) :
    budget ≤ rest + allowance I C B D := by
  obtain ⟨tag, first, hf, hnext⟩ := (bind_eq_some _ _ _ _).mp h
  obtain ⟨_, hfirst, hhead⟩ := BudgetedSeparatorCall.value _ _ _ _ _ hf
  obtain ⟨l, available, hl, hr⟩ := (bind_eq_some _ _ _ _).mp hnext
  have hlv := (BudgetedCompressionJoin.run_value I P z B D.first.right D.second.right
    (CompressionCallbacks.report I C) D.fuel₀ D.fuel₁ (D.fuel₀ + D.fuel₁ + 1)
    D.first.state D.second.state (CompressionCallbacks.empty I C) first l available hl).1
  have hlr := BudgetedCompressionJoin.run_remaining I P z B D.first.right D.second.right
    (CompressionCallbacks.report I C) D.fuel₀ D.fuel₁ (D.fuel₀ + D.fuel₁ + 1)
    D.first.state D.second.state (CompressionCallbacks.empty I C) first hn l available hl
  change l = (leftFull I C B D).1 at hlv
  dsimp only [allowance, leftBill]
  rw [← hlv]
  split at hr
  next ho =>
    rw [ite_eq_left ho]
    simp only [BudgetedSeparatorFlow.pure, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl⟩
    omega
  next ho =>
    rw [ite_eq_right ho]
    obtain ⟨r, left, hr, hp⟩ := (bind_eq_some _ _ _ _).mp hr
    have hrv := (BudgetedCompressionJoin.run_value I P (t - z) B D.third.right D.fourth.right
      (CompressionCallbacks.probe I l.state.user.val.keys.tree t)
      D.fuel₂ D.fuel₃ (D.fuel₂ + D.fuel₃ + 1) D.third.state D.fourth.state false
      available r left hr).1
    have hrr := BudgetedCompressionJoin.run_remaining I P (t - z) B D.third.right D.fourth.right
      (CompressionCallbacks.probe I l.state.user.val.keys.tree t)
      D.fuel₂ D.fuel₃ (D.fuel₂ + D.fuel₃ + 1) D.third.state D.fourth.state false
      available hn r left hr
    change r = (rightFull I B D l.state.user.val.keys.tree).1 at hrv
    dsimp only [rightBill]
    rw [← hrv]
    simp only [BudgetedSeparatorFlow.pure, Option.some.injEq, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩
    omega

end LowSpaceSubsetSum.BudgetedCompressionPass

end OAI
