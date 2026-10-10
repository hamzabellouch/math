import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.GuardMachineBase

namespace OAI

namespace MatchingFPRAS.BoolPostCompiler
open Turing MachineCost
open scoped Classical

def up : PointedMap Bool Symbol := ⟨fun b=>if b then 1 else 0,rfl⟩
def down : PointedMap Symbol Bool := ⟨fun a=>decide (a=1),rfl⟩
lemma down_up (b : Bool) : down (up b)=b := by cases b <;> decide
variable {Λ : Type*} [Inhabited Λ]
variable (M : TM0.Machine Bool Λ) (S : Finset Λ) (hS : TM0.Supports M (S : Set Λ))
def lift : TM0.Machine Symbol Λ := TM0.Machine.map M up down id id
include hS
lemma lift_supported : TM0.Supports (lift M) (S : Set Λ) := by
  refine ⟨hS.1,?_⟩
  intro q a q' s he hq
  change (q',s) ∈ (M q (down a)).map (Prod.map id (TM0.Stmt.map up)) at he
  obtain ⟨⟨r,t⟩,hr,heq⟩:=Option.map_eq_some_iff.mp he
  have hqr : r=q' := congrArg Prod.fst heq
  subst r
  exact hS.2 hr hq
omit hS in
lemma step_map (c : TM0.Cfg Bool Λ) :
    (TM0.step M c).map (TM0.Cfg.map up id)=
      TM0.step (lift M) (TM0.Cfg.map up id c) :=
  TM0.Machine.map_step M up down id id (S:=Set.univ) down_up (fun _ _=>rfl) c trivial
omit hS in
lemma advance_map (c : TM0.Cfg Bool Λ) :
    advance (TM0.step (lift M)) (TM0.Cfg.map up id c)=
      TM0.Cfg.map up id (advance (TM0.step M) c) := by
  unfold advance
  rw [←step_map]
  cases TM0.step M c <;> rfl
omit hS in
lemma run_map (c : TM0.Cfg Bool Λ) (n : ℕ) :
    MachineCost.run (TM0.step (lift M)) n (TM0.Cfg.map up id c)=
      TM0.Cfg.map up id (MachineCost.run (TM0.step M) n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [MachineCost.run,advance_map,ih]; rfl
omit hS in
lemma init_map (input : List Bool) :
    TM0.Cfg.map (Λ:=Λ) up id (TM0.init input)=TM0.init (input.map up) := by
  exact TM0.map_init up ⟨id,rfl⟩ input
noncomputable def compiled : RandomMachine := PostCompiler.sealedMachine (lift M) S
  (lift_supported M S hS)

theorem compiled_words (input output : List Bool) (n t : ℕ)
    (hhalt : TM0.step M (MachineCost.run (TM0.step M) n (TM0.init input))=none)
    (hout : (MachineCost.run (TM0.step M) n (TM0.init input)).Tape.right₀=
      ListBlank.mk output)
    (ht : n+2 ≤ t) (bits : Fin t → Bool) :
    (MatchingFPRAS.run (compiled M S hS) (input.map up) bits).state=none ∧
      (MatchingFPRAS.run (compiled M S hS) (input.map up) bits).tape.right₀=
        ListBlank.mk (output.map up) := by
  have he : MachineCost.run (TM0.step (lift M)) n (TM0.init (input.map up))=
      TM0.Cfg.map up id (MachineCost.run (TM0.step M) n (TM0.init input)) := by
    rw [←init_map,run_map]
  have hh : TM0.step (lift M) (MachineCost.run (TM0.step (lift M)) n
      (TM0.init (input.map up)))=none := by
    rw [he,←step_map,hhalt]
    rfl
  have ho : (MachineCost.run (TM0.step (lift M)) n
      (TM0.init (input.map up))).Tape.right₀=ListBlank.mk (output.map up) := by
    rw [he]
    change ((MachineCost.run (TM0.step M) n (TM0.init input)).Tape.map up).right₀=_
    have hm : ∀ T : Tape Bool,(T.map up).right₀=T.right₀.map up := by
      intro T
      obtain ⟨L,R,rfl⟩:=T.exists_mk'
      simp only [Tape.map_mk',Tape.mk'_right₀]
    rw [hm,hout,ListBlank.map_mk]
  exact PostCompiler.words_extend (compiled M S hS) (input.map up) (output.map up) ht bits
    (PostCompiler.seal_words (lift M) S (lift_supported M S hS) (input.map up)
      (output.map up) n hh ho _)
end MatchingFPRAS.BoolPostCompiler

end OAI
