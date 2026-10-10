import Mathlib
import OAI.Probability.LogConcave.Numerics.ScalarPicard

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree
open scoped Classical

variable {d : ℕ}

def RoutineBudget (B : ℕ) (η₀ η₁ : ℝ) : {k : RoutineKind} → RoutineValue d k → Prop
  | .mean,M => ∀r σ,MeanBudget B r (M r σ)
  | .sample,S => ∀r η,η=η₀ ∨ η=η₁ → SampleBudget B r η (S r η)

lemma RoutineBudget.mono {B C : ℕ} {η₀ η₁ : ℝ} {k : RoutineKind} {R : RoutineValue d k}
    (h : RoutineBudget B η₀ η₁ R) (hBC : B≤C) : RoutineBudget C η₀ η₁ R := by
  cases k with
  | mean => exact fun r σ => (h r σ).mono hBC
  | sample => exact fun r η hη => (h r η hη).mono hBC

theorem constructRoutine_budget (C : CircuitParameters) {t : ℝ} (ht : 0<t) (hs : t≤1/44)
    (c : ℕ) (η₁ : ℝ) (hD : 0<C.D)
    (hcm : ∀r σ,cost (C.meanTree (d:=d) r σ)≤c)
    (hcs : ∀r η,η=Real.sqrt (1-C.T^2)/C.T ∨ η=η₁ →
      ∀hη : 0<η, ∀hη1 : η≤1,cost (C.sampleTree (d:=d) r η hη hη1)≤c) :
    ∀L,((2*(40*c+40)^L.rank t : ℕ):ℝ)≤C.D^2 →
      RoutineBudget (2*(40*c+40)^L.rank t) (Real.sqrt (1-C.T^2)/C.T) η₁
        (constructRoutine d C ht hs L) := by
  let K := 40*c+40
  have hK : 0<K := by dsimp [K]; omega
  have hp (n : ℕ) : 2≤2*K^n := by have := Nat.one_le_pow n _ hK; omega
  apply routine_induction ht hs
  · intro L hL hcap
    rw [constructRoutine,dite_eq_left hL]
    cases L with | mk k b p =>
      cases k with
      | mean => exact fun r σ => (terminalMeanProgram_budget r σ).mono (hp _)
      | sample => exact fun r η _ => (terminalReservedProgram_budget r η).mono (hp _)
  · intro L hL ih hcap
    let n := L.rank t-1
    let B := 2*K^n
    have hi : (RoutineLabel.mk .mean (L.b-10*t) (L.p-1/4)).rank t<L.rank t :=
      RoutineStep.rank_lt ht hs hL (by cases L; exact RoutineStep.internal _ .mean _ _)
    have hpos : 0<L.rank t := by omega
    have hn : n+1=L.rank t := by dsimp [n]; omega
    have hB : 1≤B := (by have := hp n; exact le_trans (by omega) this)
    have hBparent : B≤2*K^L.rank t := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hK (by dsimp [n]; omega))
    have hBD : (B:ℝ)≤C.D^2 := le_trans (by exact_mod_cast hBparent) hcap
    have hbfinal : K*B=2*K^L.rank t := by rw [←hn]; dsimp [B]; rw [pow_succ]; ring
    have child (L' : RoutineLabel) (hh : RoutineStep t L L') :
        RoutineBudget B (Real.sqrt (1-C.T^2)/C.T) η₁ (constructRoutine d C ht hs L') := by
      have hr := hh.rank_lt ht hs hL
      have hb : 2*K^L'.rank t≤B := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hK (by dsimp [n]; omega))
      exact (ih L' hh (le_trans (by exact_mod_cast hb.trans hBparent) hcap)).mono hb
    rw [constructRoutine,dite_eq_right hL]
    cases L with | mk k b p =>
      cases k with
      | mean =>
        have hf := child ⟨.mean,b+t,p⟩ (RoutineStep.meanFinal b p)
        have hi := child ⟨.mean,b-10*t,p-1/4⟩ (RoutineStep.internal .mean .mean b p)
        have hs' := child ⟨.sample,b-10*t,p-1/4⟩ (RoutineStep.internal .mean .sample b p)
        intro r σ
        have hh := C.meanFrom_budget hB hD hBD
          (constructRoutine d C ht hs ⟨.mean,b+t,p⟩)
          (constructRoutine d C ht hs ⟨.mean,b-10*t,p-1/4⟩)
          (constructRoutine d C ht hs ⟨.sample,b-10*t,p-1/4⟩)
          (fun s r σ _ => by cases s; exact hi r σ; exact hf r σ)
          (fun r _ => hs' r _ (Or.inl rfl)) r σ (hcm r σ)
        rw [show (40*c+40)*B=2*(40*c+40)^({kind:=RoutineKind.mean,b:=b,p:=p}:RoutineLabel).rank t from hbfinal] at hh
        exact hh
      | sample =>
        have hf := child ⟨.mean,b,p⟩ (RoutineStep.sampleFinal b p)
        have hi := child ⟨.mean,b-10*t,p-1/4⟩ (RoutineStep.internal .sample .mean b p)
        intro r η hη
        have hh := C.sampleFrom_budget hB hD hBD
          (constructRoutine d C ht hs ⟨.mean,b,p⟩)
          (constructRoutine d C ht hs ⟨.mean,b-10*t,p-1/4⟩)
          (fun s r σ _ => by cases s; exact hi r σ; exact hf r σ) r η
          (fun _ hηpos hη1 => hcs r η hη hηpos hη1)
        rw [show (40*c+40)*B=2*(40*c+40)^({kind:=RoutineKind.sample,b:=b,p:=p}:RoutineLabel).rank t from hbfinal] at hh
        exact hh
end LogConcaveSampling.OracleCompiler

end

end

end OAI
