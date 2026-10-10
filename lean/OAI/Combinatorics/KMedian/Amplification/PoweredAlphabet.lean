import Mathlib
import OAI.Combinatorics.KMedian.Amplification.LabelTransport
import OAI.Combinatorics.KMedian.Amplification.PoweringConstruction
import OAI.Combinatorics.KMedian.PCP.BinaryReduction

namespace OAI

section Inline_PCPPoweredAlphabet

namespace MetricKMedian.PCP
open scoped Classical

namespace PortCSP
variable {V D K : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
variable [Fintype K] [DecidableEq K] {G : PortGraph V D}
variable (C : PortCSP G (BitVector K)) (t cap : ℕ)
variable [Fintype (Advice.BitIndex D K cap)] [DecidableEq (Advice.BitIndex D K cap)]

omit [Fintype V] [Nonempty V] [Nonempty D] in
theorem powered_reduced_complete (x : V → BitVector K) (hx : C.Satisfies x) :
    ∃ a, (AlphabetReduction.binary ((C.powered (cap := cap) t).mapLabels
      (Advice.bitsEquiv D K cap))).Satisfies a := by
  have hp := C.powered_complete (cap := cap) x hx t
  have hm := ((C.powered (cap := cap) t)).mapLabels_complete (Advice.bitsEquiv D K cap)
    (G.honest x) hp
  exact AlphabetReduction.binary_complete _ _ hm

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPoweredAlphabet

end OAI
