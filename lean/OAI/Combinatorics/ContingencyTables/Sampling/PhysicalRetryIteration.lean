import OAI.Combinatorics.ContingencyTables.Machines.OnlineIntegerRetry

namespace OAI

/-! # Composing physical retry prefixes with a uniform cost per attempt -/

namespace ContingencyTables.PhysicalRetryIteration
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost

def repeatTrial {B : Type} (p : Experiment (Option B)) : ℕ → Experiment (Option B)
  | 0 => .done none
  | N+1 => p.bind (fun b => b.elim (repeatTrial p N) (fun b => .done (some b)))

theorem repeat_cost {B : Type} (p : Experiment (Option B)) (N : ℕ) : (repeatTrial p N).cost ≤ N*p.cost := by
  induction N with
  | zero => simp [repeatTrial,Experiment.cost]
  | succ N ih =>
    have hc:=Experiment.cost_bind_le p
      (fun b => b.elim (repeatTrial p N) (fun b => .done (some b))) (N*p.cost) (by
        intro b; cases b
        · exact ih
        · exact Nat.zero_le _)
    simpa only [repeatTrial,Nat.succ_mul,Nat.add_comm] using hc

theorem repeat_implements {Γ Q B : Type} [Inhabited Γ] (M : Table Γ Q)
    (out : Option B → Cfg Γ Q) (c : Cfg Γ Q) (hc : out none=c)
    (p : Experiment (Option B)) (hp : Implements M out c p) (N : ℕ) :
    Implements M out c (repeatTrial p N) := by
  induction N with
  | zero => simpa only [repeatTrial,hc] using (Implements.done (M := M) (out := out) none)
  | succ N ih =>
    apply hp.bind _ out
    intro b
    cases b with
    | none => simpa only [Option.elim_none,hc] using ih
    | some b => exact .done (some b)

lemma repeat_mean {A B : Type} (f : A → Experiment (Option B)) (a : A)
    (p : Experiment (Option B)) (hp : ∀ g,p.mean g=(f a).mean g) (N : ℕ)
    (g : Option B → ℚ) :
    (repeatTrial p N).mean g=(OnlineIntegerRetry.prefixExperiment (f := f) a N).mean g := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [repeatTrial,OnlineIntegerRetry.prefixExperiment,Experiment.mean_bind,
      Experiment.mean_bind,hp]
    congr 1
    funext b
    cases b <;> simp only [Option.elim_none,Option.elim_some,ih]

variable {A B : Type} [TreeTyped.Codec A] [TreeTyped.Codec B] [Inhabited B]
variable {f : A → Experiment (Option B)} (F : OnlineTree.Realizer f)

/-- Compiling one attempt and composing its execution proof avoids any
growth of the compiler overhead with the number of preceding attempts. -/
theorem linear_physical_prefix (a : A) (s : TreeData.Data) (H : ℕ)
    (hH : StackCost.StackBound
      (OnlineTree.initial (OnlineIntegerRetry.program F) (TreeTyped.encode a) s).stk H)
    (N : ℕ) :
    ∃ q,PhysicalPost.Implements
      (OnlineStack.table (OnlineIntegerRetry.program F).code (OnlineIntegerRetry.program F).coin)
      (fun b => OnlineStack.cfg (OnlineControl.cfg (OnlineIntegerRetry.instructions F)
        (OnlineIntegerRetry.output a s b).1 (OnlineIntegerRetry.output a s b).2))
      (OnlineStack.cfg (OnlineTree.initial (OnlineIntegerRetry.program F) (TreeTyped.encode a) s)) q ∧
      (∀ g : Option B → ℚ,q.mean g=
        (OnlineIntegerRetry.prefixExperiment (f := f) a N).mean g) ∧
      q.cost ≤ N*(OnlineIntegerRetry.stepCost F a*
        OnlineStack.Executes.factor (OnlineIntegerRetry.program F).code H
          (OnlineIntegerRetry.stepCost F a)) := by
  obtain ⟨p,hp,hpm,hpc⟩:=OnlineIntegerRetry.physical_prefix F a s 1 H hH
  simp only [one_mul] at hpc
  have hm : ∀ g,p.mean g=(f a).mean g := by
    intro g
    rw [hpm,OnlineIntegerRetry.prefixExperiment,Experiment.mean_bind]
    congr 1
    funext b
    cases b <;> rfl
  refine ⟨repeatTrial p N,repeat_implements _ _ _ rfl p hp N,repeat_mean f a p hm N,?_⟩
  exact (repeat_cost p N).trans (Nat.mul_le_mul_left N hpc)

end ContingencyTables.PhysicalRetryIteration

end OAI
