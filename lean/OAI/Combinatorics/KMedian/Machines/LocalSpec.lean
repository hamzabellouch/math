import Mathlib
import OAI.Combinatorics.KMedian.Machines.BlendSpec
import OAI.Combinatorics.KMedian.Machines.MatchingSpec

namespace OAI

section Inline_PCPLocalSpec
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder RegularProgram

variable {A : Type} [Fintype A] [DecidableEq A]
variable (t : CSPTable A) (h : t.WellFormed)
noncomputable abbrev localGraph := FlexibleCloud.regularGraph (C t h) (cloudEmbed (C t h) (EO t))
noncomputable abbrev localCSP := FlexibleCloud.regularCSP (C t h) (cloudEmbed (C t h) (EO t))
omit [Fintype A] [DecidableEq A] in
lemma localRotate_correct (p : CloudCopies.Node (C t h)) (d : RPort) :
    localRotate t (nodeCode (C t h) (VO t) p) d=
      (nodeCode (C t h) (VO t) ((localGraph t h).step p d),(localGraph t h).back p d) := by
  unfold localGraph FlexibleCloud.regularGraph
  rw [PortGraph.blend_coded]
  rcases d with ⟨i,u,d⟩
  cases u
  by_cases hi : i=0
  · simp only [localRotate,ite_eq_left hi,matchStep_correct t h]
  · simp only [localRotate,ite_eq_right hi,nodeCode_eq t h,cloud_table t h,RotationTable.lookup_table]
    rfl
lemma localAllowed_correct (p : CloudCopies.Node (C t h)) (d : RPort) :
    localAllowed t (nodeCode (C t h) (VO t) p) d=(localCSP t h).allowed (p,d) := by
  unfold localAllowed localCSP FlexibleCloud.regularCSP PortCSP.blend
  dsimp only
  split_ifs
  · exact matchAllowed_correct t h p
  · ext q
    simp only [CloudCopies.equalityCSP,Finset.mem_filter,Finset.mem_univ,true_and]
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPLocalSpec

end OAI
