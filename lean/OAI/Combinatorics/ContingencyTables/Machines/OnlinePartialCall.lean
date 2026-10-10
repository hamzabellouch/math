import OAI.Combinatorics.ContingencyTables.Machines.OnlineRetryPrefix

namespace OAI

/-! # Calling the actual retry loop without pretending it has halted -/

namespace ContingencyTables.OnlinePartialCall
open MatchingFPRAS MatchingFPRAS.TreeData
open MatchingFPRAS.TreeMachine (Env K encodeEnv)
open MatchingFPRAS.OnlineStack MatchingFPRAS.OnlineControl
open MatchingFPRAS.PhysicalStream Turing

variable {R Λ α : Type} [DecidableEq R]

def embed (M : Λ → Instr R Λ) (l : Λ) :
    (procedure (M l)).Label → Label M := fun u => .inr ⟨l,u⟩

def callCfg (M : Λ → Instr R Λ) (l : Λ)
    (c : TM2.Cfg (fun _ : K R => Bool) (procedure (M l)).Label RegisterProc.Store) :=
  StackComposition.mapCfg (embed M l) ((successor (M l)).map Sum.inl) c

/-- A finite prefix of a called procedure can end at a live internal label.
Only actual halts return to the continuation label. -/
theorem partial_call (M : Λ → Instr R Λ) (l : Λ)
    (hcall : ∃ P next, M l = .call P next) (E : Env R)
    (out : α → TM2.Cfg (fun _ : K R => Bool) (procedure (M l)).Label RegisterProc.Store)
    (p : Experiment α)
    (hp : Executes (procedure (M l)).code (procedure (M l)).coin out
      ⟨some default,none,encodeEnv E⟩ p) :
    Executes (code M) (coins M) (fun a => callCfg M l (out a))
      (OnlineControl.cfg M (some l) E) (.delay 1 p) := by
  have hh := hp.relabel (code M) (coins M) (embed M l)
    ((successor (M l)).map Sum.inl) (fun _ => rfl) (fun _ => rfl)
  obtain ⟨P,next,h⟩ := hcall
  apply Executes.step _ _ _ _ rfl
  simpa only [OnlineControl.cfg,code,h,TM2.stepAux,callCfg,StackComposition.mapCfg_some,embed] using hh

abbrev Config (M : Λ → Instr R Λ) :=
  TM2.Cfg (fun _ : K R => Bool) (Label M) RegisterProc.Store

def At (M : Λ → Instr R Λ) (out : α → Config M)
    (l : Option Λ) (E : Env R) (p : Experiment α) : Prop :=
  Executes (code M) (coins M) out (OnlineControl.cfg M l E) p

lemma halt (M : Λ → Instr R Λ) (out : α → Config M)
    (l : Λ) (h : M l=.halt) (a : α) (E : Env R) (ha : out a=OnlineControl.cfg M none E) :
    At M out (some l) E (.delay 1 (.done a)) := by
  apply Executes.step _ _ _ _ rfl
  simp only [code,h,TM2.stepAux]
  change Executes (code M) (coins M) out (OnlineControl.cfg M none E) (.done a)
  rw [←ha]
  exact .done a

lemma nilBranch (M : Λ → Instr R Λ) (out : α → Config M)
    (l a b : Λ) (i : R) (h : M l=.branch i a b)
    (E : Env R) (hi : E i=.nil) (p : Experiment α)
    (hp : At M out (some a) E p) : At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,encodeEnv,hi,encode,List.head?_cons,
    Option.getD_some,Bool.cond_false,OnlineControl.cfg,Option.map_some] using hp

lemma consBranch (M : Λ → Instr R Λ) (out : α → Config M)
    (l a b : Λ) (i : R) (h : M l=.branch i a b)
    (E : Env R) (x y : Data) (hi : E i=.cons x y) (p : Experiment α)
    (hp : At M out (some b) E p) : At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,encodeEnv,hi,encode,List.head?_cons,
    Option.getD_some,Bool.cond_true,OnlineControl.cfg,Option.map_some] using hp

lemma call {β : Type} (M : Λ → Instr R Λ) (out : α → Config M)
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
  have hb:=hh.bind p out (fun b => by
    simpa only [At,OnlineControl.cfg,StackComposition.mapCfg_none,h,successor,Option.map_some] using hp b)
  simpa only [code,h,TM2.stepAux,StackComposition.mapCfg_some] using hb

lemma deterministicCall (M : Λ → Instr R Λ) (out : α → Config M)
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

end ContingencyTables.OnlinePartialCall

end OAI
