import Mathlib
import OAI.Combinatorics.KMedian.Amplification.FlexibleCloud

namespace OAI

section Inline_PCPMatchingLaws
namespace MetricKMedian.PCP.FlexibleCloud
open scoped Classical

variable {V E A : Type} [Fintype E] (C : BinaryCSP V E A)
variable (embed : ∀ v : CloudCopies.Active C, CloudCopies.Incident C v ↪ CloudCopies.Copy C v)
lemma matching_step_image (d : CloudCopies.Dart (E := E)) :
    (matchingGraph C embed).step (dartEmbed C embed d) ()=dartEmbed C embed (CloudCopies.dartFlip d) := by
  unfold matchingGraph
  rw [PortGraph.extend_step_image]
  rfl
lemma matching_step_outside (p : CloudCopies.Node C) (hp : p∉Set.range (dartEmbed C embed)) :
    (matchingGraph C embed).step p ()=p := by
  exact congrArg Prod.fst ((CloudCopies.dartGraph (E := E)).extend_rotate_outside (dartEmbed C embed) (p,()) hp)
variable [Fintype A] [DecidableEq A]
lemma matching_allowed_image (d : CloudCopies.Dart (E := E)) :
    (matchingCSP C embed).allowed (dartEmbed C embed d,())=(CloudCopies.dartCSP C).allowed (d,()) := by
  exact (CloudCopies.dartCSP C).extendedAllowed_image (dartEmbed C embed) (d,())
lemma matching_allowed_outside (p : CloudCopies.Node C) (hp : p∉Set.range (dartEmbed C embed)) :
    (matchingCSP C embed).allowed (p,())=Finset.univ := by
  exact (CloudCopies.dartCSP C).extendedAllowed_outside (dartEmbed C embed) (p,()) hp
end MetricKMedian.PCP.FlexibleCloud

end Inline_PCPMatchingLaws

end OAI
