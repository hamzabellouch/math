import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.OnlineTree
import OAI.Combinatorics.MatchingCount.Machines.OnlineControl

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeData TreeMachine RegisterProc TreeFunction TreeTyped
open Turing MachineCost PhysicalStream OnlineStack

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]
namespace Second
open OnlineControl

inductive Point where | split | save | body | pop | cons | halt
  deriving DecidableEq, Inhabited
instance : Fintype Point := ⟨{.split,.save,.body,.pop,.cons,.halt},by intro p; cases p <;> simp⟩
def code (P : OnlineProc.Proc (K Reg)) : Point → OnlineControl.Instr Reg Point
  | .split => .call (OnlineProc.deterministic (TreeFunction.split 1 0 (by decide))) .save
  | .save => .call (OnlineProc.deterministic (TreeFunction.cons 1 2 (by decide))) .body
  | .body => .call P .pop
  | .pop => .call (OnlineProc.deterministic (TreeFunction.split 1 2 (by decide))) .cons
  | .cons => .call (OnlineProc.deterministic (TreeFunction.cons 1 0 (by decide))) .halt
  | .halt => .halt
lemma runs {f : B → Experiment C} (F : Realizer f) (a : A) (b : B) (s : Data) :
    ∃ q,At (code F.program) (fun ac : A×C=>env (encode ac) .nil s) (Option.some Point.split)
      (env (encode (a,b)) .nil s) q ∧
      (∀ g : A×C → ℚ,q.mean g=(f b).mean (fun c=>g (a,c))) ∧
      q.cost ≤ F.cost b+8*TreeFunction.size (encode a)+22 := by
  let M:=code F.program
  let out:=fun ac : A×C=>env (encode ac) .nil s
  have hend c:=OnlineControl.halt M out Point.halt rfl (a,c)
  have hcons c:=deterministicCall M out Point.cons Point.halt
    (TreeFunction.cons 1 0 (by decide)) rfl _ _ _ (cons10 (encode c) (encode a) s) _ (hend c)
  choose pc hc hmc hcc using hcons
  have hpop c:=deterministicCall M out Point.pop Point.cons
    (TreeFunction.split 1 2 (by decide)) rfl _ _ _ (split12 (encode c) .nil (encode a) s) _ (hc c)
  choose pp hp hmp hcp using hpop
  obtain ⟨r,hr,hmr,hcr⟩:=F.correct b (.cons (encode a) s)
  have hbody:=call M out Point.body Point.pop F.program rfl
    (env (encode b) .nil (.cons (encode a) s)) (fun c=>env (encode c) .nil (.cons (encode a) s))
    r hr pp hp
  obtain ⟨p2,hp2,hm2,hc2⟩:=deterministicCall M out Point.save Point.body
    (TreeFunction.cons 1 2 (by decide)) rfl _ _ _ (cons12 (encode b) (encode a) s) _ hbody
  obtain ⟨p1,hp1,hm1,hc1⟩:=deterministicCall M out Point.split Point.save
    (TreeFunction.split 1 0 (by decide)) rfl _ _ _ (split10 (encode a) (encode b) .nil s) _ hp2
  refine ⟨p1,hp1,?_,?_⟩
  · intro g
    rw [hm1,hm2,Experiment.mean,Experiment.mean_bind]
    simp_rw [hmp,hmc,Experiment.mean]
    exact hmr _
  · have hb : ∀ c,(pp c).cost ≤ 4*TreeFunction.size (encode a)+11 := by
      intro c
      have h1:=hcc c
      have h2:=hcp c
      simp only [Experiment.cost,size_nil] at h1 h2
      omega
    have hbind:=Experiment.cost_bind_le r pp _ hb
    simp only [Experiment.cost,size_nil] at hc1 hc2
    omega
end Second

noncomputable def mapSecond {f : B → Experiment C} (F : Realizer f) :
    Realizer (fun ab : A×B=>(f ab.2).map (Prod.mk ab.1)) where
  program := OnlineControl.compile (Second.code F.program)
  cost := fun ab=>F.cost ab.2+8*TreeFunction.size (encode ab.1)+22
  correct := by
    intro ab s
    obtain ⟨q,hq,hm,hc⟩:=Second.runs F ab.1 ab.2 s
    exact ⟨q,hq,fun g=>by rw [Experiment.mean_map]; exact hm g,hc⟩

noncomputable def pair {f : A → Experiment B} {g : A → Experiment C}
    (F : Realizer f) (G : Realizer g) :
    Realizer (fun a=>(f a).bind (fun b=>(g a).map (Prod.mk b))) :=
  (composition (deterministic (TreeTyped.pair (TreeTyped.identity (A:=A)) TreeTyped.identity))
    (composition (mapSecond F)
      (composition (deterministic (TreeTyped.pair (TreeTyped.second (A:=A) (B:=B)) TreeTyped.first))
        (mapSecond G)))).congr (by
      intro a h
      simp only [Experiment.mean_bind,Experiment.mean,Experiment.mean_map,id_eq])
end MatchingFPRAS.OnlineTree

end OAI
