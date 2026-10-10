import OAI.Combinatorics.MatchingCount.Machines.OnlineControl

namespace OAI

/-! # Finite execution prefixes of the unbounded exact-rejection loop -/

namespace ContingencyTables.OnlineRetryPrefix
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.PhysicalStream
open MatchingFPRAS.TreeMachine (Env K encodeEnv)
open MatchingFPRAS.RegisterProc MatchingFPRAS.OnlineStack
open MatchingFPRAS.OnlineControl Turing

variable {R Λ α : Type} [DecidableEq R]

/-- A failed finite prefix ends at the live retry label, while a successful
prefix ends in the machine's halted configuration. -/
def At (M : Λ → Instr R Λ) (out : α → Option Λ×Env R)
    (l : Option Λ) (E : Env R) (p : Experiment α) : Prop :=
  Executes (code M) (coins M) (fun a => OnlineControl.cfg M (out a).1 (out a).2) (OnlineControl.cfg M l E) p

lemma done (M : Λ → Instr R Λ) (out : α → Option Λ×Env R) (a : α) :
    At M out (out a).1 (out a).2 (.done a) := .done a

lemma halt (M : Λ → Instr R Λ) (out : α → Option Λ×Env R)
    (l : Λ) (h : M l=.halt) (a : α) (ha : (out a).1=none) :
    At M out (some l) (out a).2 (.delay 1 (.done a)) := by
  apply Executes.step _ _ _ _ rfl
  have hd:=done M out a
  simpa only [At,code,h,TM2.stepAux,OnlineControl.cfg,ha,Option.map_none] using hd

lemma go (M : Λ → Instr R Λ) (out : α → Option Λ×Env R)
    (l k : Λ) (h : M l=.go k) (E : Env R) (p : Experiment α)
    (hp : At M out (some k) E p) :
    At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,OnlineControl.cfg,Option.map_some] using hp

lemma nilBranch (M : Λ → Instr R Λ) (out : α → Option Λ×Env R)
    (l a b : Λ) (i : R) (h : M l=.branch i a b)
    (E : Env R) (hi : E i=.nil) (p : Experiment α)
    (hp : At M out (some a) E p) :
    At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,encodeEnv,hi,encode,List.head?_cons,
    Option.getD_some,Bool.cond_false,OnlineControl.cfg,Option.map_some] using hp

lemma consBranch (M : Λ → Instr R Λ) (out : α → Option Λ×Env R)
    (l a b : Λ) (i : R) (h : M l=.branch i a b)
    (E : Env R) (x y : Data) (hi : E i=.cons x y) (p : Experiment α)
    (hp : At M out (some b) E p) :
    At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,encodeEnv,hi,encode,List.head?_cons,
    Option.getD_some,Bool.cond_true,OnlineControl.cfg,Option.map_some] using hp

lemma call {β : Type} (M : Λ → Instr R Λ) (out : α → Option Λ×Env R)
    (l next : Λ) (P : OnlineProc.Proc (K R)) (h : M l=.call P next)
    (E : Env R) (F : β → Env R) (q : Experiment β)
    (hq : Executes P.code P.coin (fun b => ⟨none,none,encodeEnv (F b)⟩)
      ⟨some default,none,encodeEnv E⟩ q)
    (p : β → Experiment α) (hp : ∀ b,At M out (some next) (F b) (p b)) :
    At M out (some l) E (.delay 1 (q.bind p)) := by
  have hq' : Executes (procedure (M l)).code (procedure (M l)).coin
      (fun b => ⟨none,none,encodeEnv (F b)⟩) ⟨some default,none,encodeEnv E⟩ q := by
    rw [show procedure (M l)=P by rw [h]; rfl]
    exact hq
  have hh:=hq'.relabel (code M) (coins M) (fun u => Sum.inr ⟨l,u⟩)
    ((successor (M l)).map Sum.inl) (fun _ => rfl) (fun _ => rfl)
  apply Executes.step _ _ _ _ rfl
  have hb:=hh.bind p (fun a => OnlineControl.cfg M (out a).1 (out a).2) (fun b => by
    simpa only [At,OnlineControl.cfg,StackComposition.mapCfg_none,h,successor,Option.map_some] using hp b)
  simpa only [code,h,TM2.stepAux,StackComposition.mapCfg_some] using hb

lemma deterministicCall (M : Λ → Instr R Λ) (out : α → Option Λ×Env R)
    (l next : Λ) (P : RegisterProc.Proc (K R))
    (h : M l=.call (OnlineProc.deterministic P) next)
    (E F : Env R) (n : ℕ) (he : RegisterProc.Exec P (encodeEnv E) (encodeEnv F) n)
    (p : Experiment α) (hp : At M out (some next) F p) :
    ∃ q,At M out (some l) E q ∧ (∀ f : α → ℚ,q.mean f=p.mean f) ∧
      q.cost ≤ n+1+p.cost := by
  obtain ⟨k,hk,he⟩:=he
  obtain ⟨r,hr,hm,hc⟩:=Executes.of_run P.code k _ _ _ he
  refine ⟨.delay 1 (r.bind (fun _ => p)),
    call M out l next (OnlineProc.deterministic P) h E (fun _ : Unit => F)
      r hr (fun _ => p) (fun _ => hp),?_,?_⟩
  · intro f
    simpa only [Experiment.mean,Experiment.mean_bind] using hm (fun _ => p.mean f)
  · have hh:=Experiment.cost_bind_le r (fun _ => p) p.cost (fun _ => le_rfl)
    simp only [Experiment.cost]
    omega

end ContingencyTables.OnlineRetryPrefix

end OAI
