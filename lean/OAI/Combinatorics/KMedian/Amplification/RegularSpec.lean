import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PaddingSpec
import OAI.Combinatorics.KMedian.Amplification.RegularGraphLaws
import OAI.Combinatorics.KMedian.Machines.LocalSpec

namespace OAI

section Inline_PCPRegularSpec
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder RegularProgram

variable {A : Type} [Fintype A] [DecidableEq A]
variable (t : CSPTable A) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
noncomputable abbrev padGraph := FlexibleRegularization.padGraph (C t h) (cloudEmbed (C t h) (EO t)) (padding t h)
noncomputable abbrev padCSP := FlexibleRegularization.padded (C t h) (cloudEmbed (C t h) (EO t)) (padding t h)
noncomputable abbrev regularGraph := FlexibleRegularization.graph (C t h) (cloudEmbed (C t h) (EO t)) (padding t h)
noncomputable abbrev regularCSP := FlexibleRegularization.csp (C t h) (cloudEmbed (C t h) (EO t)) (padding t h)
omit [Fintype A] [DecidableEq A] in
lemma paddedRotate_correct (v : GlobalRegularization.Node (C t h)) (d : RPort) :
    paddedRotate t (vertexCode t h v) d=
      (vertexCode t h ((padGraph t h).step v d),(padGraph t h).back v d) := by
  by_cases hv : v∈Set.range (padding t h)
  · obtain ⟨p,rfl⟩ := hv
    rw [paddedRotate,ite_eq_left (padding_index_lt t h p),padding_get t h,Option.getD_some]
    dsimp only
    rw [localRotate_correct t h]
    have he := FlexibleRegularization.padded_rotate_image (C t h) (cloudEmbed (C t h) (EO t)) (padding t h) p d
    change _=(vertexCode t h ((padGraph t h).rotate (padding t h p,d)).1,
      ((padGraph t h).rotate (padding t h p,d)).2)
    rw [he]
    rw [padding_index]
  · have hn := mt (padding_range t h v).mpr hv
    rw [paddedRotate,ite_eq_right hn]
    have he := FlexibleRegularization.padded_rotate_outside (C t h) (cloudEmbed (C t h) (EO t)) (padding t h) v d hv
    change (vertexCode t h v,d)=(vertexCode t h ((padGraph t h).rotate (v,d)).1,
      ((padGraph t h).rotate (v,d)).2)
    rw [he]
lemma paddedAllowed_correct (v : GlobalRegularization.Node (C t h)) (d : RPort) :
    paddedAllowed t (vertexCode t h v) d=(padCSP t h).allowed (v,d) := by
  by_cases hv : v∈Set.range (padding t h)
  · obtain ⟨p,rfl⟩ := hv
    rw [paddedAllowed,ite_eq_left (padding_index_lt t h p),padding_get t h,Option.getD_some,
      localAllowed_correct t h]
    exact (FlexibleRegularization.padded_allowed_image (C t h) (cloudEmbed (C t h) (EO t)) (padding t h) p d).symm
  · have hn := mt (padding_range t h v).mpr hv
    rw [paddedAllowed,ite_eq_right hn]
    exact (FlexibleRegularization.padded_allowed_outside (C t h) (cloudEmbed (C t h) (EO t)) (padding t h) v d hv).symm
omit [Fintype A] [DecidableEq A] in
lemma strongRotate_correct (v : GlobalRegularization.Node (C t h)) (d : GlobalRegularization.StrongPort) :
    strongRotate t (vertexCode t h v) d=
      (vertexCode t h ((GlobalRegularization.strong (C t h)).step v d),
        (GlobalRegularization.strong (C t h)).back v d) := by
  unfold strongRotate
  rw [global_table t h]
  exact RotationTable.fourthLookup_table _ _ v d
omit [Fintype A] [DecidableEq A] in
lemma rotate_correct (v : GlobalRegularization.Node (C t h)) (d : Port) :
    rotate t (vertexCode t h v) d=
      (vertexCode t h ((regularGraph t h).step v d),(regularGraph t h).back v d) := by
  rw [FlexibleRegularization.graph_coded]
  unfold rotate
  split_ifs
  · rw [paddedRotate_correct t h]
  · rw [strongRotate_correct t h]
lemma allowed_correct (v : GlobalRegularization.Node (C t h)) (d : Port) :
    allowed t (vertexCode t h v) d=(regularCSP t h).allowed (v,d) := by
  unfold regularCSP FlexibleRegularization.csp PortCSP.blend allowed
  dsimp only
  split_ifs
  · exact paddedAllowed_correct t h v d.2.1
  · rfl
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPRegularSpec

end OAI
