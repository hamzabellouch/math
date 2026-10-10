import Mathlib
import OAI.Combinatorics.KMedian.Amplification.FlexibleAmplifier
import OAI.Combinatorics.KMedian.Amplification.PowerCompleteness

namespace OAI

section Inline_PCPFlexibleComplete
namespace MetricKMedian.PCP.FlexibleAmplifier
open Amplifier
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
variable (C : BinaryCSP V E Label)
variable (cloudEmbed : ∀ v : CloudCopies.Active C, CloudCopies.Incident C v ↪ CloudCopies.Copy C v)
variable (padEmbed : CloudCopies.Node C ↪ GlobalRegularization.Node C)
omit [Fintype V] [Nonempty E] in
lemma bits_complete (x : V → Label) (hx : C.Satisfies x) :
    ∃ a, (bits C cloudEmbed padEmbed).Satisfies a := by
  obtain ⟨b,hb⟩ := FlexibleRegularization.complete C cloudEmbed padEmbed x hx
  exact (FlexibleRegularization.csp C cloudEmbed padEmbed).powered_bits_complete steps radius b hb
end MetricKMedian.PCP.FlexibleAmplifier

end Inline_PCPFlexibleComplete

end OAI
