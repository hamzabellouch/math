import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotRowBody

namespace OAI

namespace KS.W17.PivotRowLoop
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

structure Outcome where
  index : ℕ
  remaining : ℕ
  found : Bool

def entry {n : ℕ} (M : DenseRatMatrix (n+1)) (a : ℕ) : ℚ :=
  if h : a < n+1 then DenseRatMatrix.decode M 0 ⟨a,h⟩ else 0

def outcome {n : ℕ} (M : DenseRatMatrix (n+1)) (a : ℕ) : ℕ → Outcome
  | 0 => ⟨a,0,false⟩
  | k+1 => if entry M a = 0 then outcome M (a+1) k else ⟨a,k,true⟩

def state {n : ℕ} (M : DenseRatMatrix (n+1)) (a k : ℕ) (found : Bool) : Fin 32 → List Bool :=
  fun j => if j=31 then KS.W08.denseMatrixTape M else
    if j=26 then Computability.encodeNat (n+1) else if j=28 then Computability.encodeNat a else
    if j=25 then List.replicate k true else if j=24 then if found then [true] else [] else []

def guard (heads : Fin 32 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 32 :=
  if (heads 24).val ≠ 0 ∨ (heads 25).val = 0 then
    ⟨.halt, Vector.ofFn (fun _ => .stay)⟩
  else ⟨.call, Vector.ofFn (fun j => if j=25 then .pop else .stay)⟩
def program : Program 32 := KS.W29.FixedLoop.loop PivotRowBody.program guard

def config (s : Fin 32 → List Bool) : Config 32 program.states := ⟨some program.initial,s⟩

def entryTicks {n : ℕ} (M : DenseRatMatrix (n+1)) (b a : ℕ) : ℕ :=
  if h : a < n+1 then PivotRowBody.ticks M b ⟨a,h⟩ else 0

def ticks {n : ℕ} (M : DenseRatMatrix (n+1)) (b a : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => 1 + entryTicks M b a + if entry M a = 0 then ticks M b (a+1) k else 1

theorem step_empty {n : ℕ} (M : DenseRatMatrix (n+1)) (a : ℕ) (coin : Bool) :
    program.toMachine.step (config (state M a 0 false)) coin = ⟨none,state M a 0 false⟩ := by
  change (KS.W29.FixedLoop.loop PivotRowBody.program guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState PivotRowBody.program),_⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply congrArg₂ Config.mk
  · simp [KS.W29.FixedLoop.guardInstruction, guard, state, observedHeads, KS.W29.topCode]; rfl
  · funext j; simp [KS.W29.FixedLoop.guardInstruction, guard, state, observedHeads,
      KS.W29.topCode, Instruction.action, KS.W29.StackAction.apply]

theorem step_found {n : ℕ} (M : DenseRatMatrix (n+1)) (a k : ℕ) (coin : Bool) :
    program.toMachine.step (config (state M a k true)) coin = ⟨none,state M a k true⟩ := by
  change (KS.W29.FixedLoop.loop PivotRowBody.program guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState PivotRowBody.program),_⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply congrArg₂ Config.mk
  · simp [KS.W29.FixedLoop.guardInstruction, guard, state, observedHeads, KS.W29.topCode]; rfl
  · funext j; simp [KS.W29.FixedLoop.guardInstruction, guard, state, observedHeads,
      KS.W29.topCode, Instruction.action, KS.W29.StackAction.apply]

theorem step_call {n : ℕ} (M : DenseRatMatrix (n+1)) (a k : ℕ) (coin : Bool) :
    program.toMachine.step (config (state M a (k+1) false)) coin =
      KS.W29.FixedLoop.liftBody PivotRowBody.program
        ⟨some PivotRowBody.program.initial,state M a k false⟩ := by
  change (KS.W29.FixedLoop.loop PivotRowBody.program guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState PivotRowBody.program),_⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply congrArg₂ Config.mk
  · simp [KS.W29.FixedLoop.guardInstruction, guard, state,
      observedHeads, KS.W29.topCode, List.replicate_succ]
  · funext j
    by_cases hj : j=25 <;>
      simp [KS.W29.FixedLoop.guardInstruction, guard, state, observedHeads,
        KS.W29.topCode, Instruction.action, KS.W29.StackAction.apply, List.replicate_succ, hj]

theorem body_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (b a k : ℕ) (ha : a < n+1)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b) :
    RunSpec PivotRowBody.program (state M a k false)
      (if entry M a = 0 then state M (a+1) k false else state M a k true) (entryTicks M b a) := by
  have hw : KS.W07.SchurReadStage.WorkClear (state M a k false) := by
    intro j hj
    have h24 : j ≠ 24 := by intro h; subst j; omega
    have h25 : j ≠ 25 := by intro h; subst j; omega
    have h26 : j ≠ 26 := by intro h; subst j; omega
    have h28 : j ≠ 28 := by intro h; subst j; omega
    have h31 : j ≠ 31 := by intro h; subst j; omega
    simp [state,h24,h25,h26,h28,h31]
  have h := PivotRowBody.full_spec M b hnum hden ⟨a,ha⟩ (state M a k false) hw rfl rfl rfl rfl rfl
  convert h using 1
  · by_cases hz : entry M a = 0
    · have hq : DenseRatMatrix.decode M 0 ⟨a,ha⟩ = 0 := by simpa [entry,ha] using hz
      simp only [hz, ite_true, PivotRowBody.after, hq]
      funext j; fin_cases j <;> simp [state, Function.update]
    · have hq : DenseRatMatrix.decode M 0 ⟨a,ha⟩ ≠ 0 := by simpa [entry,ha] using hz
      simp only [hz, ite_false, PivotRowBody.after, hq]
      funext j; fin_cases j <;> simp [state, Function.update]
  · simp [entryTicks,ha]

theorem run_scan {n : ℕ} (M : DenseRatMatrix (n+1)) (b a k : ℕ)
    (hbound : a+k ≤ n+1)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^b)
    (bits : List Bool) (hlen : ticks M b a k ≤ bits.length) :
    program.toMachine.run (config (state M a k false)) bits =
      let o := outcome M a k
      ⟨none,state M o.index o.remaining o.found⟩ := by
  induction k generalizing a bits with
  | zero =>
    cases bits with
    | nil => simp [ticks] at hlen
    | cons coin bs =>
      erw [Machine.run.eq_2,step_empty,Machine.run_halted _ _ rfl]
      rfl
  | succ k ih =>
    have ha : a<n+1 := by omega
    have hb := body_spec M b a k ha hnum hden
    cases bits with
    | nil => simp [ticks] at hlen
    | cons coin bs =>
      have ht : entryTicks M b a ≤ bs.length := by simp only [ticks,List.length_cons] at hlen; omega
      obtain ⟨remaining,hr,hreturn⟩ := hb.loop_body_then guard bs ht
      erw [Machine.run.eq_2,step_call]
      change (KS.W29.FixedLoop.loop PivotRowBody.program guard).toMachine.run _ bs = _
      erw [hreturn]
      by_cases hz : entry M a = 0
      · have hremaining : ticks M b (a+1) k ≤ remaining.length := by
          simp only [ticks,hz,ite_true,List.length_cons] at hlen
          omega
        have hi := ih (a+1) (by omega) remaining hremaining
        simp only [hz,ite_true,outcome] at hi ⊢
        exact hi
      · have hn : 1 ≤ remaining.length := by
          simp only [ticks,hz,ite_false,List.length_cons] at hlen
          omega
        simp only [hz,ite_false,outcome]
        cases remaining with
        | nil => simp at hn
        | cons c cs =>
          change program.toMachine.run (config (state M a k true)) (c :: cs) = _
          erw [Machine.run.eq_2,step_found,Machine.run_halted _ _ rfl]

end KS.W17.PivotRowLoop

end OAI
