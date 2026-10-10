import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeCompiler
import OAI.Combinatorics.MatchingCount.Tapes.OnlineComposition

namespace OAI

namespace MatchingFPRAS.OnlineControl
open TreeData TreeMachine RegisterProc Turing MachineCost PhysicalStream OnlineStack

variable {R Λ α : Type} [DecidableEq R]
inductive Instr (R Λ : Type) where
  | halt
  | go (next : Λ)
  | branch (i : R) (nil cons : Λ)
  | call (P : OnlineProc.Proc (K R)) (next : Λ)

def procedure : Instr R Λ → OnlineProc.Proc (K R)
  | .call P _ => P
  | _ => OnlineProc.deterministic (atom .halt)
def successor : Instr R Λ → Option Λ
  | .call _ l => some l
  | _ => none
abbrev Label (M : Λ → Instr R Λ) := Λ ⊕ ((l : Λ) × (procedure (M l)).Label)
instance (M : Λ → Instr R Λ) [Fintype Λ] : Fintype (Label M) := by unfold Label; infer_instance

def code (M : Λ → Instr R Λ) : Label M → TM2.Stmt (fun _ : K R=>Bool) (Label M) Store
  | .inl l => match M l with
    | .halt => .halt
    | .go k => .goto (fun _=>.inl k)
    | .branch i a b => .peek (.inl i) (fun _ x=>x) (.branch (fun x=>x.getD false)
        (.load (fun _=>none) (.goto (fun _=>.inl b)))
        (.load (fun _=>none) (.goto (fun _=>.inl a))))
    | .call _ _ => .goto (fun _=>.inr ⟨l,default⟩)
  | .inr ⟨l,u⟩ => StackComposition.relabel (fun u=>.inr ⟨l,u⟩)
      ((successor (M l)).map Sum.inl) ((procedure (M l)).code u)
def coins (M : Λ → Instr R Λ) : CoinTM1.Coins (Label M)
  | .inl _ => none
  | .inr ⟨l,u⟩ => ((procedure (M l)).coin u).map (fun g b=>.inr ⟨l,g b⟩)
def compile [Fintype Λ] [Inhabited Λ] (M : Λ → Instr R Λ) : OnlineProc.Proc (K R) :=
  { toProc := { Label := Label M, entry := ⟨.inl default⟩, code := code M }, coin := coins M }
def cfg (M : Λ → Instr R Λ) (l : Option Λ) (E : Env R) : TM2.Cfg (fun _ : K R=>Bool) (Label M) Store :=
  ⟨l.map Sum.inl,none,encodeEnv E⟩
def At (M : Λ → Instr R Λ) (out : α → Env R) (l : Option Λ) (E : Env R) (p : Experiment α) : Prop :=
  Executes (code M) (coins M) (fun a=>cfg M none (out a)) (cfg M l E) p

lemma done (M : Λ → Instr R Λ) (out : α → Env R) (a : α) :
    At M out none (out a) (.done a) := .done a
lemma halt (M : Λ → Instr R Λ) (out : α → Env R) (l : Λ) (h : M l=.halt) (a : α) :
    At M out (some l) (out a) (.delay 1 (.done a)) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,cfg,Option.map_none] using done M out a
lemma go (M : Λ → Instr R Λ) (out : α → Env R) (l k : Λ) (h : M l=.go k)
    (E : Env R) (p : Experiment α) (hp : At M out (some k) E p) :
    At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,cfg,Option.map_some] using hp
lemma nilBranch (M : Λ → Instr R Λ) (out : α → Env R) (l a b : Λ) (i : R)
    (h : M l=.branch i a b) (E : Env R) (hi : E i=.nil)
    (p : Experiment α) (hp : At M out (some a) E p) :
    At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,encodeEnv,hi,encode,List.head?_cons,Option.getD_some,Bool.cond_false,
    cfg,Option.map_some] using hp
lemma consBranch (M : Λ → Instr R Λ) (out : α → Env R) (l a b : Λ) (i : R)
    (h : M l=.branch i a b) (E : Env R) (x y : Data) (hi : E i=.cons x y)
    (p : Experiment α) (hp : At M out (some b) E p) :
    At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,encodeEnv,hi,encode,List.head?_cons,Option.getD_some,Bool.cond_true,
    cfg,Option.map_some] using hp

lemma call {β : Type} (M : Λ → Instr R Λ) (out : α → Env R) (l next : Λ)
    (P : OnlineProc.Proc (K R)) (h : M l=.call P next)
    (E : Env R) (F : β → Env R) (q : Experiment β)
    (hq : Executes P.code P.coin (fun b=>⟨none,none,encodeEnv (F b)⟩)
      ⟨some default,none,encodeEnv E⟩ q)
    (p : β → Experiment α) (hp : ∀ b,At M out (some next) (F b) (p b)) :
    At M out (some l) E (.delay 1 (q.bind p)) := by
  have hq' : Executes (procedure (M l)).code (procedure (M l)).coin
      (fun b=>⟨none,none,encodeEnv (F b)⟩) ⟨some default,none,encodeEnv E⟩ q := by
    rw [show procedure (M l)=P by rw [h]; rfl]
    exact hq
  have hh := hq'.relabel (code M) (coins M) (fun u=>Sum.inr ⟨l,u⟩)
    ((successor (M l)).map Sum.inl) (fun _=>rfl) (fun _=>rfl)
  apply Executes.step _ _ _ _ rfl
  have hb := hh.bind p (fun a=>cfg M none (out a)) (fun b=>by
    simpa only [At,cfg,Option.map_none,StackComposition.mapCfg_none,h,successor,Option.map_some] using hp b)
  simpa only [code,h,TM2.stepAux,StackComposition.mapCfg_some] using hb

lemma deterministicCall (M : Λ → Instr R Λ) (out : α → Env R) (l next : Λ)
    (P : RegisterProc.Proc (K R)) (h : M l=.call (OnlineProc.deterministic P) next)
    (E F : Env R) (n : ℕ) (he : RegisterProc.Exec P (encodeEnv E) (encodeEnv F) n)
    (p : Experiment α) (hp : At M out (some next) F p) :
    ∃ q,At M out (some l) E q ∧ (∀ f : α → ℚ,q.mean f=p.mean f) ∧ q.cost ≤ n+1+p.cost := by
  obtain ⟨k,hk,he⟩:=he
  obtain ⟨r,hr,hm,hc⟩:=Executes.of_run P.code k _ _ _ he
  refine ⟨.delay 1 (r.bind (fun _=>p)),call M out l next (OnlineProc.deterministic P) h E (fun _ : Unit=>F)
    r hr (fun _=>p) (fun _=>hp),?_,?_⟩
  · intro f
    simpa only [Experiment.mean,Experiment.mean_bind] using hm (fun _=>p.mean f)
  · have hh:=Experiment.cost_bind_le r (fun _=>p) p.cost (fun _=>le_rfl)
    simp only [Experiment.cost]
    omega
end MatchingFPRAS.OnlineControl

end OAI
