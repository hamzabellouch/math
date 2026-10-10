import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.OnlineTree
import OAI.Combinatorics.MatchingCount.Machines.OnlineControl

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeData TreeMachine RegisterProc TreeFunction TreeTyped
open Turing MachineCost PhysicalStream OnlineStack

variable {A B : Type} [Codec A] [Codec B]

def foldM (f : A×B → Experiment B) : List A → B → Experiment B
  | [],b => .done b
  | a::as,b => (f (a,b)).bind (foldM f as)
namespace Fold
open OnlineControl
open TreeTyped.Fold (Point)

def code (P : OnlineProc.Proc (K Reg)) : Point → OnlineControl.Instr Reg Point
  | .loop => .call (OnlineProc.deterministic (TreeFunction.split 1 0 (by decide))) .check
  | .check => .branch 1 .halt .splitHead
  | .splitHead => .call (OnlineProc.deterministic (TreeFunction.split 3 1 (by decide))) .pushTail
  | .pushTail => .call (OnlineProc.deterministic (TreeFunction.cons 1 2 (by decide))) .pushArgs
  | .pushArgs => .call (OnlineProc.deterministic (TreeFunction.cons 3 0 (by decide))) .body
  | .body => .call P .popTail
  | .popTail => .call (OnlineProc.deterministic (TreeFunction.split 1 2 (by decide))) .rebuild
  | .rebuild => .call (OnlineProc.deterministic (TreeFunction.cons 1 0 (by decide))) .loop
  | .halt => .halt
noncomputable def cost (f : A×B → Experiment B) (t : A×B → ℕ) : List A → B → ℕ
  | [],_ => 10
  | a::as,b => t (a,b)+6*TreeFunction.size (encode a)+8*TreeFunction.size (encode as)+34+
      (f (a,b)).worst (cost f t as)

lemma runs {f : A×B → Experiment B} (F : Realizer f) (as : List A) (b : B) (s : Data) :
    ∃ q,At (code F.program) (fun b=>env (encode b) .nil s) (Option.some Point.loop)
      (env (encode (as,b)) .nil s) q ∧
      (∀ g : B → ℚ,q.mean g=(foldM f as b).mean g) ∧ q.cost ≤ cost f F.cost as b := by
  induction as generalizing b with
  | nil =>
    have hh := OnlineControl.halt (code F.program) (fun b=>env (encode b) .nil s) Point.halt rfl b
    have hc := OnlineControl.nilBranch (code F.program) (fun b=>env (encode b) .nil s)
      Point.check Point.halt Point.splitHead 1 rfl _ rfl _ hh
    obtain ⟨q,hq,hm,hcost⟩:=deterministicCall (code F.program) (fun b=>env (encode b) .nil s)
      Point.loop Point.check (TreeFunction.split 1 0 (by decide)) rfl _ _ _
      (split10 .nil (encode b) .nil s) _ hc
    refine ⟨q,hq,?_,?_⟩
    · intro g; simpa only [Experiment.mean,foldM] using hm g
    · simpa only [cost,size_nil,Experiment.cost] using hcost
  | cons a as ih =>
    choose q hq hm hcost using ih
    let out := fun b : B=>env (encode b) .nil s
    let M := code F.program
    let sr := TreeFunction.size (encode as)
    let sa := TreeFunction.size (encode a)
    have hreb v := deterministicCall M out Point.rebuild Point.loop
      (TreeFunction.cons 1 0 (by decide)) rfl _ _ _
      (cons10 (encode v) (encode as) s) (q v) (hq v)
    choose qr hr hmr hcr using hreb
    have hpop v := deterministicCall M out Point.popTail Point.rebuild
      (TreeFunction.split 1 2 (by decide)) rfl _ _ _
      (split12 (encode v) .nil (encode as) s) (qr v) (hr v)
    choose qp hp hmp hcp using hpop
    obtain ⟨r,hrf,hrm,hrc⟩:=F.correct (a,b) (.cons (encode as) s)
    have hbody := call M out Point.body Point.popTail F.program rfl
      (env (encode (a,b)) .nil (.cons (encode as) s))
      (fun v=>env (encode v) .nil (.cons (encode as) s)) r hrf qp hp
    have h4 := TreeTyped.Fold.pushArgs (encode a) (encode b) (encode as) s
    obtain ⟨p4,hp4,hm4,hc4⟩:=deterministicCall M out Point.pushArgs Point.body
      (TreeFunction.cons 3 0 (by decide)) rfl _ _ _ h4 _ hbody
    have h5 := TreeTyped.Fold.pushTail (encode a) (encode b) (encode as) s
    obtain ⟨p5,hp5,hm5,hc5⟩:=deterministicCall M out Point.pushTail Point.pushArgs
      (TreeFunction.cons 1 2 (by decide)) rfl _ _ _ h5 _ hp4
    have h6 := TreeTyped.Fold.splitHeads (encode a) (encode b) (encode as) s
    obtain ⟨p6,hp6,hm6,hc6⟩:=deterministicCall M out Point.splitHead Point.pushTail
      (TreeFunction.split 3 1 (by decide)) rfl _ _ _ h6 _ hp5
    have hc := OnlineControl.consBranch M out Point.check Point.halt Point.splitHead
      1 rfl (env (encode b) (encode (a::as)) s) (encode a) (encode as) rfl p6 hp6
    obtain ⟨p7,hp7,hm7,hc7⟩:=deterministicCall M out Point.loop Point.check
      (TreeFunction.split 1 0 (by decide)) rfl _ _ _
      (split10 (encode (a::as)) (encode b) .nil s) _ hc
    refine ⟨p7,hp7,?_,?_⟩
    · intro g
      rw [hm7,Experiment.mean,hm6,hm5,hm4,Experiment.mean,Experiment.mean_bind]
      simp_rw [hmp,hmr,hm]
      simpa only [foldM,Experiment.mean_bind] using hrm (fun v=>(foldM f as v).mean g)
    · have hcq : ∀ v,(qp v).cost ≤ 4*sr+10+cost f F.cost as v := by
        intro v
        have hr':=(hcr v)
        have hp':=(hcp v)
        have ht:=hcost v
        simp only [size_nil] at hp'
        dsimp [sr] at *
        omega
      have ha : r.All (fun v=>(qp v).cost ≤ 4*sr+10+(f (a,b)).worst (cost f F.cost as)) := by
        apply (Experiment.all_of_mean_eq hrm _ (Experiment.all_worst (f (a,b)) (cost f F.cost as))).mono
        intro v hv
        exact (hcq v).trans (Nat.add_le_add_left hv _)
      have hbind:=Experiment.cost_bind_le_of_all r qp _ ha
      simp only [Experiment.cost,size_nil,encode_list_cons,size_cons] at hc4 hc7
      simp only [cost]
      dsimp [sr,sa] at *
      omega
end Fold

noncomputable def fold {f : A×B → Experiment B} (F : Realizer f) :
    Realizer (fun ab : List A×B=>foldM f ab.1 ab.2) where
  program := OnlineControl.compile (Fold.code F.program)
  cost := fun ab=>Fold.cost f F.cost ab.1 ab.2
  correct := by
    intro ab s
    obtain ⟨q,hq,hm,hc⟩:=Fold.runs F ab.1 ab.2 s
    exact ⟨q,hq,hm,hc⟩
end MatchingFPRAS.OnlineTree

end OAI
