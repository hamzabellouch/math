import Mathlib
import OAI.Combinatorics.KMedian.Amplification.LabelTransport
import OAI.Combinatorics.KMedian.Amplification.PaddedAlphabet
import OAI.Combinatorics.KMedian.Amplification.PoweringConstruction

namespace OAI

section Inline_PCPPaddedPowered
namespace MetricKMedian.PCP.PortCSP
open scoped Classical

variable {V D K : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
variable [Fintype K] [DecidableEq K] {G : PortGraph V D}
variable (C : PortCSP G (BitVector K)) (t cap : ℕ)
variable [Fintype (Advice.BitIndex D K cap)] [DecidableEq (Advice.BitIndex D K cap)]
omit [Fintype V] [Nonempty V] [Nonempty D] in
theorem powered_padded_complete (x : V → BitVector K) (hx : C.Satisfies x) :
    ∃ a, (AlphabetReduction.paddedBinary ((C.powered (cap := cap) t).mapLabels
      (Advice.bitsEquiv D K cap))).Satisfies a := by
  have hp := C.powered_complete (cap := cap) x hx t
  have hm := (C.powered (cap := cap) t).mapLabels_complete (Advice.bitsEquiv D K cap)
    (G.honest x) hp
  exact AlphabetReduction.padded_complete _ _ hm
end MetricKMedian.PCP.PortCSP

end Inline_PCPPaddedPowered

end OAI
