import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeMachine

namespace OAI

namespace MatchingFPRAS.TreeMachine
open TreeData RegisterProc Turing MachineCost

variable {R Λ : Type} [DecidableEq R]

inductive Effect : Instr R Λ → Env R → Option Λ → Env R → Prop
  | halt (E) : Effect .halt E none E
  | go (E l) : Effect (.go l) E (some l) E
  | nilBranch (E i l r) (h : E i=.nil) : Effect (.branch i l r) E (some l) E
  | consBranch (E i l r x y) (h : E i=.cons x y) : Effect (.branch i l r) E (some r) E
  | nil (E i l) : Effect (.nil i l) E (some l) (Function.update E i .nil)
  | copy (E i j h l) : Effect (.copy i j h l) E (some l) (putPair E i j (E i) (E i))
  | cons (E i j h l) : Effect (.cons i j h l) E (some l) (putPair E i j .nil (.cons (E i) (E j)))
  | split (E i j h l x y) (he : E j=.cons x y) : Effect (.split i j h l) E (some l) (putPair E i j x y)

abbrev Label (M : Λ → Instr R Λ) := Λ ⊕ ((l : Λ) × (procedure (M l)).Label)
instance (M : Λ → Instr R Λ) [Fintype Λ] : Fintype (Label M) := by unfold Label; infer_instance

def code (M : Λ → Instr R Λ) : Label M → TM2.Stmt (fun _ : K R=>Bool) (Label M) Store
  | .inl l => match M l with
    | .halt => .halt
    | .go k => .goto (fun _=>.inl k)
    | .branch i a b => .peek (.inl i) (fun _ x=>x) (.branch (fun x=>x.getD false)
        (.load (fun _=>none) (.goto (fun _=>.inl b)))
        (.load (fun _=>none) (.goto (fun _=>.inl a))))
    | _ => .goto (fun _=>.inr ⟨l,default⟩)
  | .inr ⟨l,u⟩ => StackComposition.relabel (fun u=>.inr ⟨l,u⟩)
      ((successor (M l)).map Sum.inl) ((procedure (M l)).code u)

def compile [Fintype Λ] [Inhabited Λ] (M : Λ → Instr R Λ) : Proc (K R) :=
  { Label := Label M
    entry := ⟨.inl default⟩
    code := code M }

def cfg (M : Λ → Instr R Λ) (l : Option Λ) (E : Env R) : TM2.Cfg (fun _ : K R=>Bool) (Label M) Store :=
  ⟨l.map Sum.inl,none,encodeEnv E⟩

def SizeBound (E : Env R) (B : ℕ) : Prop := ∀ i,(encode (E i)).length≤B

lemma run_procedure (M : Λ → Instr R Λ) (l : Λ) (E F : Env R) (n : ℕ)
    (h : Exec (procedure (M l)) (encodeEnv E) (encodeEnv F) n)
    (hd : code M (.inl l)=.goto (fun _=>.inr ⟨l,default⟩)) :
    ∃ k≤n+1,MachineCost.run (TM2.step (code M)) k (cfg M (some l) E)=
      cfg M (successor (M l)) F := by
  obtain ⟨j,hj,he⟩:=h
  obtain ⟨k,hk,hs⟩:=StackComposition.run_relabel_to_halt (procedure (M l)).code (code M)
    (fun u=>Sum.inr ⟨l,u⟩) ((successor (M l)).map Sum.inl) (fun _=>rfl)
    j ⟨some default,none,encodeEnv E⟩ none (encodeEnv F) he
  refine ⟨k+1,by omega,?_⟩
  rw [MachineCost.run]
  have ha : advance (TM2.step (code M)) (cfg M (some l) E)=
      StackComposition.mapCfg (fun u=>Sum.inr ⟨l,u⟩) ((successor (M l)).map Sum.inl)
        ⟨some default,none,encodeEnv E⟩ := by
    simp only [advance,TM2.step,cfg,Option.map_some,hd,TM2.stepAux,Option.getD_some,
      StackComposition.mapCfg_some]
  rw [ha,hs]
  rfl

theorem effect_compiles (M : Λ → Instr R Λ) (l : Λ) (I : Instr R Λ) (hI : M l=I)
    (E F : Env R) (next : Option Λ) (h : Effect I E next F) (B : ℕ) (hB : SizeBound E B) :
    ∃ k≤5*(B+1),MachineCost.run (TM2.step (code M)) k (cfg M (some l) E)=cfg M next F := by
  cases h with
  | halt E =>
    refine ⟨1,by omega,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,
      Option.getD_some,Option.map_none]
  | go E a =>
    refine ⟨1,by omega,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,Option.getD_some]
  | nilBranch E i a b hi =>
    refine ⟨1,by omega,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,
      encodeEnv,hi,encode,List.head?_cons,Option.getD_some,Bool.cond_false]
  | consBranch E i a b x y hi =>
    refine ⟨1,by omega,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,
      encodeEnv,hi,encode,List.head?_cons,Option.getD_some,Bool.cond_true]
  | nil E i a =>
    have hp:=nil_exec E i a
    rw [←hI] at hp
    obtain ⟨k,hk,he⟩:=run_procedure M l E _ _ hp (by simp only [code,hI])
    refine ⟨k,?_,?_⟩
    · have hi:=hB i; omega
    · simpa only [hI,successor] using he
  | copy E i j hij a =>
    have hp:=copy_exec E i j hij a
    rw [←hI] at hp
    obtain ⟨k,hk,he⟩:=run_procedure M l E _ _ hp (by simp only [code,hI])
    refine ⟨k,?_,?_⟩
    · have hi:=hB i; have hj:=hB j; omega
    · simpa only [hI,successor] using he
  | cons E i j hij a =>
    have hp:=cons_exec E i j hij a
    rw [←hI] at hp
    obtain ⟨k,hk,he⟩:=run_procedure M l E _ _ hp (by simp only [code,hI])
    refine ⟨k,?_,?_⟩
    · have hi:=hB i; omega
    · simpa only [hI,successor] using he
  | split E i j hij a x y hy =>
    have hp:=split_exec E i j hij a x y hy
    rw [←hI] at hp
    obtain ⟨k,hk,he⟩:=run_procedure M l E _ _ hp (by simp only [code,hI])
    refine ⟨k,?_,?_⟩
    · have hi:=hB i; have hj:=hB j
      rw [hy] at hj
      simp only [encode,List.length_cons,List.length_append] at hj
      omega
    · simpa only [hI,successor] using he

inductive Runs (M : Λ → Instr R Λ) (B : ℕ) : Option Λ → Env R → Env R → ℕ → Prop
  | done (E) : Runs M B none E E 0
  | step (l E next F G n) (hB : SizeBound E B) (h : Effect (M l) E next F)
      (rest : Runs M B next F G n) : Runs M B (some l) E G (n+1)

theorem runs_compiles (M : Λ → Instr R Λ) (B n : ℕ) (l : Option Λ) (E F : Env R)
    (h : Runs M B l E F n) :
    ∃ k≤n*(5*(B+1)),MachineCost.run (TM2.step (code M)) k (cfg M l E)=cfg M none F := by
  induction h with
  | done E => exact ⟨0,by simp,rfl⟩
  | step l E next F G n hB h rest ih =>
    obtain ⟨i,hi,he⟩:=effect_compiles M l (M l) rfl E F next h B hB
    obtain ⟨j,hj,hf⟩:=ih
    refine ⟨i+j,?_,?_⟩
    · calc
        i+j≤5*(B+1)+n*(5*(B+1)) := Nat.add_le_add hi hj
        _=(n+1)*(5*(B+1)) := by ring
    · rw [run_add,he,hf]

theorem compile_exec [Fintype Λ] [Inhabited Λ] (M : Λ → Instr R Λ) (B n : ℕ) (E F : Env R)
    (h : Runs M B (some default) E F n) :
    Exec (compile M) (encodeEnv E) (encodeEnv F) (n*(5*(B+1))) :=
  runs_compiles M B n (some default) E F h
end MatchingFPRAS.TreeMachine

end OAI
