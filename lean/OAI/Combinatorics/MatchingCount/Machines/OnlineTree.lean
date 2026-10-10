import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeSum
import OAI.Combinatorics.MatchingCount.Graphs.ExperimentSupport
import OAI.Combinatorics.MatchingCount.Tapes.OnlineComposition

namespace OAI

namespace MatchingFPRAS.OnlineTree
open Turing MachineCost PhysicalStream OnlineStack TreeData TreeMachine TreeFunction TreeTyped

abbrev StoreCfg (P : OnlineProc.Proc (K Reg)) := TM2.Cfg (fun _ : K Reg=>Bool) P.Label RegisterProc.Store
def initial (P : OnlineProc.Proc (K Reg)) (x s : Data) : StoreCfg P :=
  ⟨some default,none,encodeEnv (env x .nil s)⟩
def final (P : OnlineProc.Proc (K Reg)) (x s : Data) : StoreCfg P :=
  ⟨none,none,encodeEnv (env x .nil s)⟩
structure Realizer {A B : Type} [Codec A] [Codec B] (f : A → Experiment B) where
  program : OnlineProc.Proc (K Reg)
  cost : A → ℕ
  correct : ∀ a s,∃ q : Experiment B,
    Executes program.code program.coin (fun b=>final program (encode b) s)
      (initial program (encode a) s) q ∧
    (∀ g : B → ℚ,q.mean g=(f a).mean g) ∧ q.cost≤cost a
variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def deterministic {f : A → B} (F : TreeTyped.Realizer f) : Realizer (fun a=>.done (f a)) where
  program := OnlineProc.deterministic F.program
  cost := F.cost
  correct := by
    intro a s
    obtain ⟨n,hn,he⟩:=F.correct a s
    obtain ⟨p,hp,hm,hc⟩:=Executes.of_run F.program.code n _ _ _ he
    refine ⟨p.map (fun _=>f a),?_,?_,?_⟩
    · exact hp.bind (fun _=>.done (f a)) _ (fun _=>.done (f a))
    · intro g
      rw [Experiment.mean_map,hm]; rfl
    · rw [Experiment.cost_map]
      exact hc.trans hn

noncomputable def composition {f : A → Experiment B} {g : B → Experiment C}
    (F : Realizer f) (G : Realizer g) : Realizer (fun a=>(f a).bind g) where
  program := OnlineProc.seq F.program G.program
  cost := fun a=>F.cost a+(f a).worst G.cost
  correct := by
    intro a s
    obtain ⟨p,hp,hm,hc⟩:=F.correct a s
    choose q hq hqm hqc using fun b=>G.correct b s
    have hp':=hp.relabel (OnlineProc.seq F.program G.program).code (OnlineProc.seq F.program G.program).coin
      Sum.inl (some (Sum.inr default)) (fun _=>rfl) (fun _=>rfl)
    have hq' b := (hq b).relabel (OnlineProc.seq F.program G.program).code (OnlineProc.seq F.program G.program).coin
      Sum.inr none (fun _=>rfl) (fun _=>rfl)
    refine ⟨p.bind q,hp'.bind q _ hq',?_,?_⟩
    · intro h
      simp_rw [Experiment.mean_bind,hqm]
      exact hm _
    · apply (Experiment.cost_bind_le_of_all p q ((f a).worst G.cost) ?_).trans (Nat.add_le_add_right hc _)
      exact (Experiment.all_of_mean_eq hm _ (Experiment.all_worst (f a) G.cost)).mono
        (fun b hb=>(hqc b).trans hb)

def Realizer.congr {f g : A → Experiment B} (F : Realizer f)
    (h : ∀ a w,(f a).mean w=(g a).mean w) : Realizer g where
  program := F.program
  cost := F.cost
  correct := by
    intro a s
    obtain ⟨q,hq,hm,hc⟩:=F.correct a s
    exact ⟨q,hq,fun w=>(hm w).trans (h a w),hc⟩

def chooseProgram (P Q : OnlineProc.Proc (K Reg)) : OnlineProc.Proc (K Reg) where
  toProc := {
    Label := Unit ⊕ (P.Label ⊕ Q.Label)
    entry := ⟨.inl ()⟩
    code := fun l=>match l with
      | .inl _ => .halt
      | .inr (.inl l) => StackComposition.relabel (fun u=>Sum.inr (Sum.inl u)) none (P.code l)
      | .inr (.inr l) => StackComposition.relabel (fun u=>Sum.inr (Sum.inr u)) none (Q.code l) }
  coin := fun l=>match l with
    | .inl _ => some (fun b=>if b then .inr (.inr default) else .inr (.inl default))
    | .inr (.inl l) => (P.coin l).map (fun f b=>.inr (.inl (f b)))
    | .inr (.inr l) => (Q.coin l).map (fun f b=>.inr (.inr (f b)))

noncomputable def choose {f g : A → Experiment B} (F : Realizer f) (G : Realizer g) :
    Realizer (fun a=>.read (fun b=>if b then g a else f a)) where
  program := chooseProgram F.program G.program
  cost := fun a=>1+max (F.cost a) (G.cost a)
  correct := by
    intro a s
    obtain ⟨p,hp,hm,hc⟩:=F.correct a s
    obtain ⟨q,hq,hqm,hqc⟩:=G.correct a s
    have hp':=hp.relabel (chooseProgram F.program G.program).code (chooseProgram F.program G.program).coin
      (fun u=>Sum.inr (Sum.inl u)) none (fun _=>rfl) (fun _=>rfl)
    have hq':=hq.relabel (chooseProgram F.program G.program).code (chooseProgram F.program G.program).coin
      (fun u=>Sum.inr (Sum.inr u)) none (fun _=>rfl) (fun _=>rfl)
    refine ⟨.read (fun b=>if b then q else p),?_,?_,?_⟩
    · apply Executes.read _ _ _ _ _ rfl
      intro b
      cases b
      · exact hp'
      · exact hq'
    · intro h
      simp only [Experiment.mean,Bool.false_eq_true,↓reduceIte,hm,hqm]
    · simp only [Experiment.cost,Bool.false_eq_true,↓reduceIte]
      omega

noncomputable def randomBit : Realizer (fun _ : A=>.read (fun b=>.done b)) :=
  (choose (deterministic (TreeTyped.constant false)) (deterministic (TreeTyped.constant true))).congr
    (by intro a f; rfl)
end MatchingFPRAS.OnlineTree

end OAI
