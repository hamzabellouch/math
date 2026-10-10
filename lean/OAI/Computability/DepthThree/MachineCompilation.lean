import OAI.Computability.DepthThree.MachineBasic
import OAI.Computability.DepthThree.MachineFiniteRestriction
import Mathlib.Data.Finset.Lattice.Fold

namespace OAI

namespace DepthThreeLowerBound
namespace MachineCompilation

open Turing

variable {Γ Λ σ : Type}

def stmtCost : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q => stmtCost q + 1
  | .write _ q => stmtCost q + 1
  | .load _ q => stmtCost q
  | .branch _ q₁ q₂ => max (stmtCost q₁) (stmtCost q₂)
  | .goto _ => 1
  | .halt => 1

theorem stmtCost_pos (q : TM1.Stmt Γ Λ σ) : 0 < stmtCost q := by
  induction q with
  | move _ q ih => exact Nat.zero_lt_succ _
  | write _ q ih => exact Nat.zero_lt_succ _
  | load _ q ih => exact ih
  | branch _ q₁ q₂ ih₁ ih₂ => exact ih₁.trans_le (le_max_left _ _)
  | goto _ => exact Nat.zero_lt_one
  | halt => exact Nat.zero_lt_one

variable [instInhabitedΓ : Inhabited Γ] [instInhabitedΛ : Inhabited Λ] [instInhabitedσ : Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ)

def subCfg (q : TM1.Stmt Γ Λ σ) (v : σ) (tape : Tape Γ) :
    TM0.Cfg Γ (TM1to0.Λ' M) :=
  ⟨(some q, v), tape⟩

theorem stepAux_counted (q : TM1.Stmt Γ Λ σ) (v : σ) (tape : Tape Γ) :
    ∃ k, 0 < k ∧ k ≤ stmtCost q ∧
      runSteps (TM0.step (TM1to0.tr M)) k (some (subCfg M q v tape)) =
        some (TM1to0.trCfg M (TM1.stepAux q v tape)) := by
  induction q generalizing v tape with
  | move d q ih =>
      obtain ⟨k, hk, hcost, hrun⟩ := ih v (tape.move d)
      refine ⟨k + 1, Nat.succ_pos k, Nat.add_le_add_right hcost 1, ?_⟩
      rw [runSteps_succ_left]
      exact hrun
  | write a q ih =>
      obtain ⟨k, hk, hcost, hrun⟩ := ih v (tape.write (a tape.1 v))
      refine ⟨k + 1, Nat.succ_pos k, Nat.add_le_add_right hcost 1, ?_⟩
      rw [runSteps_succ_left]
      exact hrun
  | load a q ih =>
      obtain ⟨k, hk, hcost, hrun⟩ := ih (a tape.1 v) tape
      refine ⟨k, hk, hcost, ?_⟩
      have hstep :
          TM0.step (TM1to0.tr M) (subCfg M (.load a q) v tape) =
            TM0.step (TM1to0.tr M) (subCfg M q (a tape.1 v) tape) := rfl
      exact (runSteps_eq_of_step_eq hstep hk).trans hrun
  | branch p q₁ q₂ ih₁ ih₂ =>
      cases hp : p tape.1 v with
      | false =>
          obtain ⟨k, hk, hcost, hrun⟩ := ih₂ v tape
          refine ⟨k, hk, hcost.trans (le_max_right _ _), ?_⟩
          have hstep :
              TM0.step (TM1to0.tr M) (subCfg M (.branch p q₁ q₂) v tape) =
                TM0.step (TM1to0.tr M) (subCfg M q₂ v tape) := by
            simp only [subCfg, TM0.step, TM1to0.tr, TM1to0.trAux, hp, Bool.cond_false]
          have hout : TM1.stepAux (.branch p q₁ q₂) v tape =
              TM1.stepAux q₂ v tape := by
            simp only [TM1.stepAux, hp, Bool.cond_false]
          rw [hout]
          exact (runSteps_eq_of_step_eq hstep hk).trans hrun
      | true =>
          obtain ⟨k, hk, hcost, hrun⟩ := ih₁ v tape
          refine ⟨k, hk, hcost.trans (le_max_left _ _), ?_⟩
          have hstep :
              TM0.step (TM1to0.tr M) (subCfg M (.branch p q₁ q₂) v tape) =
                TM0.step (TM1to0.tr M) (subCfg M q₁ v tape) := by
            simp only [subCfg, TM0.step, TM1to0.tr, TM1to0.trAux, hp, Bool.cond_true]
          have hout : TM1.stepAux (.branch p q₁ q₂) v tape =
              TM1.stepAux q₁ v tape := by
            simp only [TM1.stepAux, hp, Bool.cond_true]
          rw [hout]
          exact (runSteps_eq_of_step_eq hstep hk).trans hrun
  | goto l =>
      refine ⟨1, Nat.zero_lt_one, le_refl 1, ?_⟩
      change some (TM0.Cfg.mk _ (tape.write tape.1)) = some (TM0.Cfg.mk _ tape)
      rw [Tape.write_self]
      rfl
  | halt =>
      refine ⟨1, Nat.zero_lt_one, le_refl 1, ?_⟩
      change some (TM0.Cfg.mk _ (tape.write tape.1)) = some (TM0.Cfg.mk _ tape)
      rw [Tape.write_self]
      rfl

variable [instFintypeΛ : Fintype Λ]

def programCost : ℕ :=
  Finset.univ.sup (fun l => stmtCost (M l))

theorem stmtCost_le_programCost
    {Γ : Type}
    {Λ : Type}
    {σ : Type}
    [Inhabited Γ]
    [Inhabited Λ]
    [Inhabited σ]
    (M : Λ → Turing.TM1.Stmt Γ Λ σ)
    [instFintypeΛ : Fintype Λ]
    (l : Λ) : stmtCost (M l) ≤ programCost M :=
  Finset.le_sup (f := fun l => stmtCost (M l)) (Finset.mem_univ l)

theorem programCost_pos : 0 < programCost M :=
  (stmtCost_pos (M default)).trans_le (stmtCost_le_programCost M default)

theorem step_counted {c c' : TM1.Cfg Γ Λ σ} (h : TM1.step M c = some c') :
    RunsIn (TM0.step (TM1to0.tr M)) (TM1to0.trCfg M c) (TM1to0.trCfg M c')
      (programCost M) := by
  rcases c with ⟨l, v, tape⟩
  cases l with
  | none => cases h
  | some l =>
      have hc : TM1.stepAux (M l) v tape = c' := Option.some.inj h
      subst c'
      obtain ⟨k, hk, hcost, hrun⟩ := stepAux_counted M (M l) v tape
      exact ⟨k, hcost.trans (stmtCost_le_programCost M l), hrun⟩

theorem run_counted (n : ℕ) {c c' : TM1.Cfg Γ Λ σ}
    (h : runSteps (TM1.step M) n (some c) = some c') :
    RunsIn (TM0.step (TM1to0.tr M)) (TM1to0.trCfg M c) (TM1to0.trCfg M c')
      (programCost M * n) := by
  induction n generalizing c with
  | zero =>
      have hc : c = c' := Option.some.inj h
      subst c'
      simpa only [Nat.mul_zero] using RunsIn.refl (TM0.step (TM1to0.tr M))
        (TM1to0.trCfg M c)
  | succ n ih =>
      rw [runSteps_succ_left] at h
      cases hstep : TM1.step M c with
      | none =>
          rw [Option.bind_some, hstep, runSteps_none] at h
          cases h
      | some d =>
          have hrest : runSteps (TM1.step M) n (some d) = some c' := by
            simpa only [Option.bind_some, hstep] using h
          simpa only [Nat.mul_succ, Nat.add_comm] using
            (step_counted M hstep).trans (ih hrest)

theorem runsIn_counted {c c' : TM1.Cfg Γ Λ σ} {bound : ℕ}
    (h : RunsIn (TM1.step M) c c' bound) :
    RunsIn (TM0.step (TM1to0.tr M)) (TM1to0.trCfg M c) (TM1to0.trCfg M c')
      (programCost M * bound) := by
  obtain ⟨n, hn, hrun⟩ := h
  exact (run_counted M n hrun).mono (Nat.mul_le_mul_left _ hn)

theorem compiled_halt
    {Γ : Type}
    {Λ : Type}
    {σ : Type}
    [instInhabitedΓ : Inhabited Γ]
    [instInhabitedΛ : Inhabited Λ]
    [instInhabitedσ : Inhabited σ]
    (M : Λ → Turing.TM1.Stmt Γ Λ σ)
    [Fintype Λ]
    {c : TM1.Cfg Γ Λ σ} (h : TM1.step M c = none) :
    TM0.step (TM1to0.tr M) (TM1to0.trCfg M c) = none := by
  rcases c with ⟨l, v, tape⟩
  cases l with
  | none => rfl
  | some l => cases h

theorem compiled_init
    {Γ : Type}
    {Λ : Type}
    {σ : Type}
    [instInhabitedΓ : Inhabited Γ]
    [instInhabitedΛ : Inhabited Λ]
    [instInhabitedσ : Inhabited σ]
    (M : Λ → Turing.TM1.Stmt Γ Λ σ)
    [Fintype Λ]
    (input : List Γ) :
    TM1to0.trCfg M (TM1.init input) = TM0.init input := rfl

theorem source_supports
    {Γ : Type}
    {Λ : Type}
    {σ : Type}
    [Inhabited Γ]
    [instInhabitedΛ : Inhabited Λ]
    [Inhabited σ]
    (M : Λ → Turing.TM1.Stmt Γ Λ σ)
    [instFintypeΛ : Fintype Λ] : TM1.Supports M Finset.univ := by
  classical
  refine ⟨Finset.mem_univ _, ?_⟩
  intro l hl
  induction M l with
  | move _ _ ih => exact ih
  | write _ _ ih => exact ih
  | load _ _ ih => exact ih
  | branch _ _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | goto _ => exact fun _ _ => Finset.mem_univ _
  | halt => trivial

variable [Fintype Γ] [Fintype σ]
variable (inputSymbol : Bool → Γ) (hinj : Function.Injective inputSymbol)
variable (hblank : ∀ b, inputSymbol b ≠ default) (accept : σ → Bool)

noncomputable def compileFinite : FiniteMachine :=
  MachineFiniteRestriction.toFiniteMachine (TM1to0.tr M)
    (TM1to0.trStmts M Finset.univ) (TM1to0.tr_supports M (source_supports M))
    inputSymbol hinj hblank (fun q => accept q.2)

theorem compileFinite_haltsIn (w : List Bool) (output : Bool) (time : ℕ)
    (c : TM1.Cfg Γ Λ σ)
    (hrun : RunsIn (TM1.step M) (TM1.init (w.map inputSymbol)) c time)
    (hhalt : TM1.step M c = none) (haccept : accept c.var = output) :
    HaltsIn (compileFinite M inputSymbol hinj hblank accept) w output
      (programCost M * time) := by
  apply (MachineFiniteRestriction.toFiniteMachine_haltsIn_iff (TM1to0.tr M)
    (TM1to0.trStmts M Finset.univ) (TM1to0.tr_supports M (source_supports M))
    inputSymbol hinj hblank (fun q => accept q.2) w output (programCost M * time)).2
  obtain ⟨k, hk, hcompiled⟩ := runsIn_counted M hrun
  refine ⟨k, hk, TM1to0.trCfg M c, ?_, compiled_halt M hhalt, haccept⟩
  simpa only [compiled_init] using hcompiled

include hinj hblank in

theorem polynomialTimeDecider_of_counted_TM1 (f : List Bool → Bool)
    (C a : ℕ) (hC : 0 < C) (ha : 0 < a)
    (hprogram : ∀ w, ∃ c : TM1.Cfg Γ Λ σ,
      RunsIn (TM1.step M) (TM1.init (w.map inputSymbol)) c
        (C * (w.length + 1) ^ a) ∧
      TM1.step M c = none ∧ accept c.var = f w) :
    PolynomialTimeDecider f := by
  refine ⟨compileFinite M inputSymbol hinj hblank accept,
    programCost M * C, a, Nat.mul_pos (programCost_pos M) hC, ha, ?_⟩
  intro w
  obtain ⟨c, hrun, hhalt, haccept⟩ := hprogram w
  simpa only [Nat.mul_assoc] using
    compileFinite_haltsIn M inputSymbol hinj hblank accept w (f w)
      (C * (w.length + 1) ^ a) c hrun hhalt haccept

end MachineCompilation
end DepthThreeLowerBound

end OAI
