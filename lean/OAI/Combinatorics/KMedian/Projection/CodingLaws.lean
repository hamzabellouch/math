import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PoweringObjects
import OAI.Combinatorics.KMedian.Projection.CSPProjection
import OAI.Combinatorics.KMedian.Projection.SeedCombinators

namespace OAI

section Inline_PCPProjectionCodingLaws
namespace MetricKMedian.PCP.Compiler.SeedCombinators
open scoped Classical

variable {T V D A : Type} [DecidableEq A]
variable (G : PortGraph V D) (C : PortCSP G A) (chosen : V×D→A×A)
variable (r : T→ℕ→D→ℕ×D) (fix : T→ℕ→D→(A×A)→A×A) (t : T) (code : V→ℕ)
variable (hr : ∀v d,r t (code v) d=(code (G.rotate (v,d)).1,(G.rotate (v,d)).2))
include hr in
omit [DecidableEq A] in
lemma source_correct (v : V) (s : D×Bool) :
    source r t (code v) s=(code ((C.projection chosen).edge.symm (v,s)).1.1,
      ((C.projection chosen).edge.symm (v,s)).1.2) := by
  cases s with | mk d b =>
    cases b
    · rfl
    · exact hr v d
variable (hf : ∀ v d a,fix t (code v) d a=C.repair chosen (v,d) a)
include hr hf in
omit [DecidableEq A] in
lemma project_correct (v : V) (s : D×Bool) :
    project r fix t (code v) s=(C.projection chosen).project ((C.projection chosen).edge.symm (v,s)) := by
  funext a
  unfold project
  rw [source_correct G C chosen r t code hr v s]
  dsimp only
  rw [hf]
  cases s with | mk d b => cases b <;> rfl
variable {m k : ℕ} (ue : V≃Fin m) (de : D≃Fin k)
omit [DecidableEq A] in
lemma numbered_correct (hr' : ∀v d,r t (ue v).val d=((ue (G.rotate (v,d)).1).val,(G.rotate (v,d)).2))
    (hf' : ∀v d a,fix t (ue v).val d a=C.repair chosen (v,d) a) (v : V) (s : D×Bool) :
    numbered r fix (fun d=>(de d).val) k t (ue v).val s=
      ((((ue.prodCongr de).trans finProdFinEquiv) ((C.projection chosen).edge.symm (v,s)).1).val,
        (C.projection chosen).project ((C.projection chosen).edge.symm (v,s))) := by
  apply Prod.ext
  · simp only [numbered,source_correct G C chosen r t (fun v=>(ue v).val) hr',
      Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map,finProdFinEquiv]
    rfl
  · exact project_correct G C chosen r fix t (fun v=>(ue v).val) hr' hf' v s
end MetricKMedian.PCP.Compiler.SeedCombinators

end Inline_PCPProjectionCodingLaws

end OAI
