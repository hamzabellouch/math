import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionJoinCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionCallbackBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.BudgetedCompressionPass

namespace OAI

/-! # Two stopped compression joins with the dictionary retained between them -/

namespace LowSpaceSubsetSum.CompressionPassCells

open CompressionContext (Context)
variable {n : ℕ} {P t z : ℤ}

def left (I : Instance n) (C B : ℕ) (D : BudgetedCompressionPass.Data P t z) (budget : ℕ) :=
  CompressionJoinCells.run I P z B D.first.right D.second.right
    (CompressionCallbackCells.report I C) CompressionCallbackCells.dictionaryCells
    D.fuel₀ D.fuel₁ (D.fuel₀+D.fuel₁+1) D.first.state D.second.state
    (CompressionCallbacks.empty I C) budget

theorem left_value (I : Instance n) (C B : ℕ) (D : BudgetedCompressionPass.Data P t z) (budget : ℕ) :
    (left I C B D budget).1 = BudgetedCompressionPass.left I C B D budget := by
  rw [left,CompressionJoinCells.value]
  have he : (fun x y a => (CompressionCallbackCells.report I C x y a).1) =
      CompressionCallbacks.report I C := by
    funext x y a
    exact CompressionCallbackCells.report_value I C x y a
  rw [he]
  rfl

def right (I : Instance n) (B : ℕ) (D : BudgetedCompressionPass.Data P t z)
    (tree : BinaryTrie.Tree) (budget : ℕ) :=
  CompressionJoinCells.run I P (t-z) B D.third.right D.fourth.right
    (CompressionCallbackCells.probe I tree t) (fun _ => 1)
    D.fuel₂ D.fuel₃ (D.fuel₂+D.fuel₃+1) D.third.state D.fourth.state false budget

theorem right_value (I : Instance n) (B : ℕ) (D : BudgetedCompressionPass.Data P t z)
    (tree : BinaryTrie.Tree) (budget : ℕ) :
    (right I B D tree budget).1 = BudgetedCompressionPass.right I B D tree budget := by
  rw [right,CompressionJoinCells.value]
  have he : (fun x y a => (CompressionCallbackCells.probe I tree t x y a).1) =
      CompressionCallbacks.probe I tree t := by
    funext x y a
    exact CompressionCallbackCells.probe_value I tree t x y a
  rw [he]
  rfl

def contextCells {P : ℤ} {mode : FilteredStream.Mode} (ctx : Context P mode) : ℕ :=
  4*ctx.right.size+CompressionReaderCells.stateCells ctx.state+16

def resident (D : BudgetedCompressionPass.Data P t z) : ℕ :=
  contextCells D.first+contextCells D.second+contextCells D.third+contextCells D.fourth+64

structure Fits (n C : ℕ) {P : ℤ} {mode : FilteredStream.Mode} (ctx : Context P mode) : Prop where
  size : ctx.right.size ≤ C
  depth : ctx.depth ≤ n
  tree : 2^(ctx.depth+1) ≤ 4*(C+1)

structure Ready (n C : ℕ) (D : BudgetedCompressionPass.Data P t z) : Prop where
  first : Fits n C D.first
  second : Fits n C D.second
  third : Fits n C D.third
  fourth : Fits n C D.fourth

theorem context_bound (C : ℕ) {P : ℤ} {mode : FilteredStream.Mode} (ctx : Context P mode)
    (h : Fits n C ctx) : contextCells ctx ≤ 148*(C+1) := by
  have ht := h.tree
  unfold contextCells
  rw [CompressionReaderCells.stateCells_exact]
  have hs := h.size
  omega

theorem resident_bound (C : ℕ) (D : BudgetedCompressionPass.Data P t z) (h : Ready n C D) :
    resident D ≤ 656*(C+1) := by
  have ha := context_bound C D.first h.first
  have hb := context_bound C D.second h.second
  have hc := context_bound C D.third h.third
  have hd := context_bound C D.fourth h.fourth
  unfold resident
  omega

def run (I : Instance n) (C B : ℕ) (D : BudgetedCompressionPass.Data P t z) (budget : ℕ) :=
  let held := resident D
  if 8 ≤ budget then
    let l := left I C B D (budget-8)
    let peak := held+l.2+32
    match l.1.1 with
    | none => ((none,8+l.1.2),peak)
    | some (out,available) =>
      if out.state.user.val.keys.overflow then ((some (false,available),8+l.1.2),peak)
      else
        let r := right I B D out.state.user.val.keys.tree available
        ((r.1.1.map (fun (out,remaining) => (out.state.user,remaining)),8+(l.1.2+r.1.2)),
          max peak (held+CompressionCallbackCells.dictionaryCells out.state.user+r.2+32))
  else ((none,1),held+8)

theorem value (I : Instance n) (C B : ℕ) (D : BudgetedCompressionPass.Data P t z) (budget : ℕ) :
    (run I C B D budget).1 = BudgetedCompressionPass.run I C B D budget := by
  unfold run BudgetedCompressionPass.run BudgetedSeparatorCall.run
  dsimp only
  split
  · simp only [BudgetedSeparatorFlow.bind,left_value]
    cases hl : (BudgetedCompressionPass.left I C B D (budget-8)).1 with
    | none => rfl
    | some p =>
      rcases p with ⟨out,available⟩
      dsimp only
      split
      · simp only [BudgetedSeparatorFlow.pure,Nat.add_zero]
      · simp only [right_value,BudgetedSeparatorFlow.pure,Nat.add_zero]
        cases (BudgetedCompressionPass.right I B D out.state.user.val.keys.tree available).1 <;> rfl
  · rfl

theorem cells (I : Instance n) (C B : ℕ) (D : BudgetedCompressionPass.Data P t z) (budget : ℕ)
    (hn : 10000 ≤ n) (hB : B ≤ C) (hD : Ready n C D) :
    (run I C B D budget).2 ≤ inputScale I^6*(C+1) := by
  let u := inputScale I
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hres := resident_bound C D hD
  have hl := CompressionJoinCells.cells I P z B D.first.right D.second.right
    (CompressionCallbackCells.report I C) CompressionCallbackCells.dictionaryCells
    D.fuel₀ D.fuel₁ (D.fuel₀+D.fuel₁+1) D.first.state D.second.state
    (CompressionCallbacks.empty I C) (budget-8) C hn hD.first.depth hD.second.depth
    hD.first.tree hD.second.tree hB (CompressionCallbackBounds.dictionary I hn C)
    (CompressionCallbackBounds.report I hn C)
  change (left I C B D (budget-8)).2 ≤ u^5*(C+1) at hl
  have hpow : u^4 ≤ u^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hlarge : 688 ≤ u^5 := by
    have hp : u ≤ u^5 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ u by omega) (by decide : 1 ≤ 5)
    omega
  have hfinal : 3*u^5*(C+1) ≤ u^6*(C+1) := by
    apply Nat.mul_le_mul_right
    calc
      _ ≤ u*u^5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  change (run I C B D budget).2 ≤ u^6*(C+1)
  unfold run
  dsimp only
  split
  · cases hleft : (left I C B D (budget-8)).1.1 with
    | none => dsimp only; nlinarith only [hres,hl,hlarge,hfinal]
    | some p =>
      rcases p with ⟨out,available⟩
      have hdict := CompressionCallbackBounds.dictionary I hn C out.state.user
      have hr := CompressionJoinCells.cells I P (t-z) B D.third.right D.fourth.right
        (CompressionCallbackCells.probe I out.state.user.val.keys.tree t) (fun _ => 1)
        D.fuel₂ D.fuel₃ (D.fuel₂+D.fuel₃+1) D.third.state D.fourth.state false available C
        hn hD.third.depth hD.fourth.depth hD.third.tree hD.fourth.tree hB
        (fun _ => by
          have hp : 1 ≤ u^4 := Nat.one_le_pow _ _ (by omega)
          exact hp.trans (Nat.le_mul_of_pos_right _ (by omega)))
        (CompressionCallbackBounds.probe I hn C out.state.user.val.keys.tree t)
      change (right I B D out.state.user.val.keys.tree available).2 ≤ u^5*(C+1) at hr
      dsimp only
      split <;> dsimp only
      · nlinarith only [hres,hl,hlarge,hfinal]
      · have hm := Nat.mul_le_mul_right (C+1) hpow
        apply max_le
        · nlinarith only [hres,hl,hlarge,hfinal]
        · nlinarith only [hres,hr,hdict,hm,hlarge,hfinal]
  · dsimp only
    nlinarith only [hres,hlarge,hfinal]

end LowSpaceSubsetSum.CompressionPassCells

end OAI
