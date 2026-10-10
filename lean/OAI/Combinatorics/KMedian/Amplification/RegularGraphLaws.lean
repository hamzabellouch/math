import Mathlib
import OAI.Combinatorics.KMedian.Amplification.FlexibleRegularization
import OAI.Combinatorics.KMedian.Machines.BlendSpec

namespace OAI

section Inline_PCPRegularGraphLaws
namespace MetricKMedian.PCP.FlexibleRegularization
open scoped Classical

variable {V E A : Type} [Fintype V] [Fintype E] [Nonempty E] [Fintype A] [DecidableEq A] [Inhabited A]
variable (C : BinaryCSP V E A)
variable (cloudEmbed : ∀ v : CloudCopies.Active C, CloudCopies.Incident C v ↪ CloudCopies.Copy C v)
variable (padEmbed : CloudCopies.Node C ↪ GlobalRegularization.Node C)
noncomputable abbrev padGraph := (FlexibleCloud.regularGraph C cloudEmbed).extend padEmbed
omit [Fintype V] [Nonempty E] [Fintype A] [DecidableEq A] [Inhabited A] in
lemma graph_coded (code : GlobalRegularization.Node C → ℕ) (v : GlobalRegularization.Node C)
    (d : GlobalRegularization.Degree) :
    (code ((graph C cloudEmbed padEmbed).step v d),(graph C cloudEmbed padEmbed).back v d)=
      if d.1=0 then (code ((padGraph C cloudEmbed padEmbed).step v d.2.1),
        (d.1,((padGraph C cloudEmbed padEmbed).back v d.2.1,d.2.2)))
      else (code ((GlobalRegularization.strong C).step v d.2.2),
        (d.1,(d.2.1,(GlobalRegularization.strong C).back v d.2.2))) :=
  PortGraph.blend_coded _ _ code v d
omit [Fintype V] [Nonempty E] [Fintype A] [DecidableEq A] [Inhabited A] in
lemma padded_rotate_image (p : CloudCopies.Node C) (d : CloudCopies.RegularPort) :
    (padGraph C cloudEmbed padEmbed).rotate (padEmbed p,d)=
      (padEmbed ((FlexibleCloud.regularGraph C cloudEmbed).step p d),
        (FlexibleCloud.regularGraph C cloudEmbed).back p d) := by
  exact (FlexibleCloud.regularGraph C cloudEmbed).extend_rotate_image padEmbed (p,d)
omit [Fintype V] [Nonempty E] [Fintype A] [DecidableEq A] [Inhabited A] in
lemma padded_rotate_outside (v : GlobalRegularization.Node C) (d : CloudCopies.RegularPort)
    (hv : v∉Set.range padEmbed) :
    (padGraph C cloudEmbed padEmbed).rotate (v,d)=(v,d) := by
  exact (FlexibleCloud.regularGraph C cloudEmbed).extend_rotate_outside padEmbed (v,d) hv
omit [Fintype V] [Nonempty E] [Inhabited A] in
lemma padded_allowed_image (p : CloudCopies.Node C) (d : CloudCopies.RegularPort) :
    (padded C cloudEmbed padEmbed).allowed (padEmbed p,d)=
      (FlexibleCloud.regularCSP C cloudEmbed).allowed (p,d) := by
  exact (FlexibleCloud.regularCSP C cloudEmbed).extendedAllowed_image padEmbed (p,d)
omit [Fintype V] [Nonempty E] [Inhabited A] in
lemma padded_allowed_outside (v : GlobalRegularization.Node C) (d : CloudCopies.RegularPort)
    (hv : v∉Set.range padEmbed) :
    (padded C cloudEmbed padEmbed).allowed (v,d)=Finset.univ := by
  exact (FlexibleCloud.regularCSP C cloudEmbed).extendedAllowed_outside padEmbed (v,d) hv
end MetricKMedian.PCP.FlexibleRegularization

end Inline_PCPRegularGraphLaws

end OAI
