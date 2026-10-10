import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeCompiler

namespace OAI

namespace MatchingFPRAS.RegisterControl
open TreeData TreeMachine RegisterProc Turing MachineCost

variable {R Λ : Type} [DecidableEq R]
inductive Instr (R Λ : Type) where
  | halt
  | go (next : Λ)
  | branch (i : R) (nil cons : Λ)
  | call (P : Proc (K R)) (next : Λ)

def procedure : Instr R Λ → Proc (K R)
  | .call P _ => P
  | _ => atom .halt
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
def compile [Fintype Λ] [Inhabited Λ] (M : Λ → Instr R Λ) : Proc (K R) :=
  { Label := Label M
    entry := ⟨.inl default⟩
    code := code M }
def cfg (M : Λ → Instr R Λ) (l : Option Λ) (E : Env R) : TM2.Cfg (fun _ : K R=>Bool) (Label M) Store :=
  ⟨l.map Sum.inl,none,encodeEnv E⟩

inductive Effect : Instr R Λ → Env R → Option Λ → Env R → ℕ → Prop
  | halt (E) : Effect .halt E none E 1
  | go (E l) : Effect (.go l) E (some l) E 1
  | nilBranch (E i l r) (h : E i=.nil) : Effect (.branch i l r) E (some l) E 1
  | consBranch (E i l r x y) (h : E i=.cons x y) : Effect (.branch i l r) E (some r) E 1
  | call (P E F l n) (h : Exec P (encodeEnv E) (encodeEnv F) n) : Effect (.call P l) E (some l) F (n+1)

lemma effect_compiles (M : Λ → Instr R Λ) (l : Λ) (I : Instr R Λ) (hI : M l=I)
    (E F : Env R) (next : Option Λ) (n : ℕ) (h : Effect I E next F n) :
    ∃ k≤n,MachineCost.run (TM2.step (code M)) k (cfg M (some l) E)=cfg M next F := by
  cases h with
  | halt E =>
    refine ⟨1,le_rfl,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,
      Option.getD_some,Option.map_none]
  | go E a =>
    refine ⟨1,le_rfl,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,Option.getD_some]
  | nilBranch E i a b hi =>
    refine ⟨1,le_rfl,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,
      encodeEnv,hi,encode,List.head?_cons,Option.getD_some,Bool.cond_false]
  | consBranch E i a b x y hi =>
    refine ⟨1,le_rfl,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,
      encodeEnv,hi,encode,List.head?_cons,Option.getD_some,Bool.cond_true]
  | call P E F a n hp =>
    have hp' : Exec (procedure (M l)) (encodeEnv E) (encodeEnv F) n := by simpa only [hI,procedure] using hp
    obtain ⟨j,hj,he⟩:=hp'
    obtain ⟨k,hk,hs⟩:=StackComposition.run_relabel_to_halt (procedure (M l)).code (code M)
      (fun u=>Sum.inr ⟨l,u⟩) ((successor (M l)).map Sum.inl) (fun _=>rfl)
      j ⟨some default,none,encodeEnv E⟩ none (encodeEnv F) he
    refine ⟨k+1,by omega,?_⟩
    rw [MachineCost.run]
    have ha : advance (TM2.step (code M)) (cfg M (some l) E)=
        StackComposition.mapCfg (fun u=>Sum.inr ⟨l,u⟩) ((successor (M l)).map Sum.inl)
          ⟨some default,none,encodeEnv E⟩ := by
      simp only [advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,Option.getD_some,
        StackComposition.mapCfg_some]
    rw [ha,hs]
    simp only [cfg,hI,successor,Option.map_some]

inductive Runs (M : Λ → Instr R Λ) : Option Λ → Env R → Env R → ℕ → Prop
  | done (E) : Runs M none E E 0
  | step (l E next F G n k) (h : Effect (M l) E next F k)
      (rest : Runs M next F G n) : Runs M (some l) E G (k+n)
  | weaken (l : Option Λ) (E F : Env R) (n b : ℕ) (h : Runs M l E F n) (hn : n ≤ b) : Runs M l E F b
lemma runs_compiles (M : Λ → Instr R Λ) (n : ℕ) (l : Option Λ) (E F : Env R)
    (h : Runs M l E F n) :
    ∃ k≤n,MachineCost.run (TM2.step (code M)) k (cfg M l E)=cfg M none F := by
  induction h with
  | done E => exact ⟨0,le_rfl,rfl⟩
  | step l E next F G n k h rest ih =>
    obtain ⟨i,hi,he⟩:=effect_compiles M l (M l) rfl E F next k h
    obtain ⟨j,hj,hf⟩:=ih
    exact ⟨i+j,Nat.add_le_add hi hj,by rw [run_add,he,hf]⟩
  | weaken l E F n m h hnm ih => obtain ⟨k,hk,he⟩:=ih; exact ⟨k,hk.trans hnm,he⟩
lemma compile_exec [Fintype Λ] [Inhabited Λ] (M : Λ → Instr R Λ) (n : ℕ) (E F : Env R)
    (h : Runs M (some default) E F n) : Exec (compile M) (encodeEnv E) (encodeEnv F) n :=
  runs_compiles M n (some default) E F h
end MatchingFPRAS.RegisterControl

end OAI
