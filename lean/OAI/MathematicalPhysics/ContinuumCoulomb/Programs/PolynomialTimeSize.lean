import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumVerifier

namespace OAI

/-! A polynomial-time TM2 program has polynomial output bit length. The
constant below counts the pushes in its finite program text, rather than
assuming an output-size estimate as an additional complexity axiom. -/

namespace ContinuumCoulomb
open Turing StateTransition
open scoped BigOperators

namespace TM2Size

/-- Maximum number of pushes along one finite statement branch. -/
def pushes {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_stack_length {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q generalizing v S with
  | push j f q ih =>
    have h := ih v (Function.update S j (f v :: S j))
    have hu : (Function.update S j (f v :: S j) k).length ≤ (S k).length + 1 := by
      by_cases hj : k = j
      · subst k; simp
      · simp [Function.update_of_ne hj]
    change ((TM2.stepAux q v (Function.update S j (f v :: S j))).stk k).length ≤ _
    unfold pushes
    omega
  | peek j f q ih => exact ih _ _
  | pop j f q ih =>
    have h := ih (f v (S j).head?) (Function.update S j (S j).tail)
    have hu : (Function.update S j (S j).tail k).length ≤ (S k).length := by
      by_cases hj : k = j
      · subst k; simp
      · simp [Function.update_of_ne hj]
    change ((TM2.stepAux q (f v (S j).head?) (Function.update S j (S j).tail)).stk k).length ≤ _
    unfold pushes
    omega
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
    change ((cond (f v) (TM2.stepAux q v S) (TM2.stepAux r v S)).stk k).length ≤ _
    cases hf : f v
    · simpa only [hf, Bool.cond_false, pushes] using (ihr v S).trans
        (Nat.add_le_add_left (le_max_right (pushes q) (pushes r)) (S k).length)
    · simpa only [hf, Bool.cond_true, pushes] using (ihq v S).trans
        (Nat.add_le_add_left (le_max_left (pushes q) (pushes r)) (S k).length)
  | goto f => simp [pushes, TM2.stepAux]
  | halt => simp [pushes, TM2.stepAux]

/-- A finite program has a fixed bound on pushes in one machine step. -/
def programPushes (tm : FinTM2) : ℕ := by
  letI := tm.ΛFin
  exact Finset.univ.sup (fun l => pushes (tm.m l))

theorem step_stack_length (tm : FinTM2) (a b : tm.Cfg) (k : tm.K)
    (h : tm.step a = some b) :
    (b.stk k).length ≤ (a.stk k).length + programPushes tm := by
  let := tm.ΛFin
  cases a with
  | mk l v S =>
    cases l with
    | none => simp [FinTM2.step, TM2.step] at h
    | some l =>
      have hb : TM2.stepAux (tm.m l) v S = b := by
        exact Option.some.inj h
      rw [← hb]
      exact (stepAux_stack_length (tm.m l) v S k).trans
        (Nat.add_le_add_left (Finset.le_sup (f := fun l => pushes (tm.m l)) (Finset.mem_univ l)) _)

theorem iterate_stack_length (tm : FinTM2) (n : ℕ) (a b : tm.Cfg) (k : tm.K)
    (h : (fun x : Option tm.Cfg => x.bind tm.step)^[n] (some a) = some b) :
    (b.stk k).length ≤ (a.stk k).length + n * programPushes tm := by
  induction n generalizing b with
  | zero =>
    have hab : a = b := by simpa only [Function.iterate_zero_apply, Option.some.injEq] using h
    subst b
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases he : (fun x : Option tm.Cfg => x.bind tm.step)^[n] (some a) with
    | none => simp only [he, Option.bind_none] at h; contradiction
    | some c =>
      have hs : tm.step c = some b := by simpa only [he, Option.bind_some] using h
      have hc := ih c he
      have hb := step_stack_length tm c b k hs
      rw [Nat.succ_mul]
      omega

theorem init_stack_length (tm : FinTM2) (L : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((initList tm L).stk k).length ≤ L.length := by
  by_cases hk : k = tm.k₀
  · subst k; simp [initList]
  · simp [initList, hk]

/-- Bit output length is bounded directly from a genuine polynomial-time
certificate; this is needed when composing the hardness reduction. -/
theorem output_length {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤ (ea a).length + h.time.eval (ea a).length * programPushes h.tm := by
  have ho := h.outputsFun a
  have hi : ((initList h.tm (List.map h.inputAlphabet.invFun (ea a))).stk h.tm.k₁).length ≤
      (ea a).length := by
    simpa only [List.length_map] using
      init_stack_length h.tm (List.map h.inputAlphabet.invFun (ea a)) h.tm.k₁
  have hv := iterate_stack_length h.tm ho.steps
    (initList h.tm (List.map h.inputAlphabet.invFun (ea a)))
    (haltList h.tm (List.map h.outputAlphabet.invFun (eb (f a)))) h.tm.k₁ ho.evals_in_steps
  have hout : ((haltList h.tm (List.map h.outputAlphabet.invFun (eb (f a)))).stk h.tm.k₁).length =
      (eb (f a)).length := by simp [haltList]
  rw [hout] at hv
  exact hv.trans (Nat.add_le_add hi (Nat.mul_le_mul_right _ ho.steps_le_m))

end TM2Size
end ContinuumCoulomb

end OAI
