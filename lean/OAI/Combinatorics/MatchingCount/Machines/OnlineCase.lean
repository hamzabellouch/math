import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.OnlineTree
import OAI.Combinatorics.MatchingCount.Machines.OnlineControl

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeData TreeMachine RegisterProc TreeFunction TreeTyped
open Turing MachineCost PhysicalStream OnlineStack

variable {A B : Type} [Codec A] [Codec B]
namespace Case
open OnlineControl

inductive Point where | split | test | yesClear | noClear | yes | no | halt
  deriving DecidableEq, Inhabited
instance : Fintype Point := ⟨{.split,.test,.yesClear,.noClear,.yes,.no,.halt},by intro p;cases p <;>simp⟩
def code (P Q : OnlineProc.Proc (K Reg)) : Point→OnlineControl.Instr Reg Point
  | .split => .call (OnlineProc.deterministic (TreeFunction.split 1 0 (by decide))) .test
  | .test => .branch 1 .noClear .yesClear
  | .yesClear => .call (OnlineProc.deterministic (TreeFunction.clear 1)) .yes
  | .noClear => .call (OnlineProc.deterministic (TreeFunction.clear 1)) .no
  | .yes => .call P .halt
  | .no => .call Q .halt
  | .halt => .halt
lemma runs {f g : A→Experiment B} (F : Realizer f) (G : Realizer g) (b : Bool) (a : A) (s : Data) :
    ∃ q,At (code F.program G.program) (fun y=>env (encode y) .nil s) (Option.some Point.split)
      (env (encode (b,a)) .nil s) q ∧
      (∀ h : B→ℚ,q.mean h=(if b then f a else g a).mean h) ∧
      q.cost≤(if b then F.cost a else G.cost a)+30 := by
  let M:=code F.program G.program
  let out:=fun y : B=>env (encode y) .nil s
  have hend y:=OnlineControl.halt M out Point.halt rfl y
  cases b with
  | false =>
    obtain ⟨r,hr,hm,hc⟩:=G.correct a s
    have hb:=call M out Point.no Point.halt G.program rfl (env (encode a) .nil s)
      (fun y=>env (encode y) .nil s) r hr (fun y=>.delay 1 (.done y)) hend
    obtain ⟨q,hq,hqm,hqc⟩:=deterministicCall M out Point.noClear Point.no
      (TreeFunction.clear 1) rfl _ _ _ (clear1 (encode a) (encode false) s) _ hb
    have ht:=nilBranch M out Point.test Point.noClear Point.yesClear 1 rfl _ rfl _ hq
    obtain ⟨v,hv,hvm,hvc⟩:=deterministicCall M out Point.split Point.test
      (TreeFunction.split 1 0 (by decide)) rfl _ _ _ (split10 (encode false) (encode a) .nil s) _ ht
    refine ⟨v,hv,?_,?_⟩
    · intro h
      rw [hvm,Experiment.mean,hqm,Experiment.mean,Experiment.mean_bind]
      exact hm h
    · have hh:=Experiment.cost_bind_le r (fun y=>.delay 1 (.done y)) 1 (fun _=>by rfl)
      simp only [Experiment.cost] at hqc hvc
      change v.cost≤G.cost a+30
      change q.cost≤1+2+1+(1+(r.bind (fun y=>.delay 1 (.done y))).cost) at hqc
      change v.cost≤1+2*1+4+1+(1+q.cost) at hvc
      omega
  | true =>
    obtain ⟨r,hr,hm,hc⟩:=F.correct a s
    have hb:=call M out Point.yes Point.halt F.program rfl (env (encode a) .nil s)
      (fun y=>env (encode y) .nil s) r hr (fun y=>.delay 1 (.done y)) hend
    obtain ⟨q,hq,hqm,hqc⟩:=deterministicCall M out Point.yesClear Point.yes
      (TreeFunction.clear 1) rfl _ _ _ (clear1 (encode a) (encode true) s) _ hb
    have ht:=consBranch M out Point.test Point.noClear Point.yesClear 1 rfl _ .nil .nil rfl _ hq
    obtain ⟨v,hv,hvm,hvc⟩:=deterministicCall M out Point.split Point.test
      (TreeFunction.split 1 0 (by decide)) rfl _ _ _ (split10 (encode true) (encode a) .nil s) _ ht
    refine ⟨v,hv,?_,?_⟩
    · intro h
      rw [hvm,Experiment.mean,hqm,Experiment.mean,Experiment.mean_bind]
      exact hm h
    · have hh:=Experiment.cost_bind_le r (fun y=>.delay 1 (.done y)) 1 (fun _=>by rfl)
      simp only [Experiment.cost] at hqc hvc
      change v.cost≤F.cost a+30
      change q.cost≤3+2+1+(1+(r.bind (fun y=>.delay 1 (.done y))).cost) at hqc
      change v.cost≤1+2*3+4+1+(1+q.cost) at hvc
      omega
end Case
noncomputable def caseBool {f g : A→Experiment B} (F : Realizer f) (G : Realizer g) :
    Realizer (fun x : Bool×A=>if x.1 then f x.2 else g x.2) where
  program := OnlineControl.compile (Case.code F.program G.program)
  cost := fun x=>(if x.1 then F.cost x.2 else G.cost x.2)+30
  correct := fun x s=>Case.runs F G x.1 x.2 s
noncomputable def conditional {p : A→Bool} {f g : A→Experiment B} (P : TreeTyped.Realizer p)
    (F : Realizer f) (G : Realizer g) : Realizer (fun a=>if p a then f a else g a) :=
  (composition (deterministic (TreeTyped.pair P TreeTyped.identity)) (caseBool F G)).congr (fun _ _=>rfl)
end MatchingFPRAS.OnlineTree

end OAI
