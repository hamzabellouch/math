import Mathlib
import OAI.Combinatorics.KMedian.Amplification.LabelTransport
import OAI.Combinatorics.KMedian.Amplification.PoweringConstruction

namespace OAI

section Inline_PCPPowerCompleteness
namespace MetricKMedian.PCP
open scoped Classical

namespace PortCSP
variable {V D K : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
variable [Fintype K] [DecidableEq K] {G : PortGraph V D}
variable (C : PortCSP G (BitVector K)) (t cap : ℕ)
variable [Fintype (Advice.BitIndex D K cap)] [DecidableEq (Advice.BitIndex D K cap)]
omit [Fintype V] [Nonempty V] [Nonempty D]
  [Fintype (Advice.BitIndex D K cap)] [DecidableEq (Advice.BitIndex D K cap)] in
lemma powered_bits_complete (x : V → BitVector K) (hx : C.Satisfies x) :
    ∃ a, ((C.powered (cap := cap) t).mapLabels (Advice.bitsEquiv D K cap)).Satisfies a := by
  exact ⟨_,(C.powered (cap := cap) t).mapLabels_complete (Advice.bitsEquiv D K cap)
    (G.honest x) (C.powered_complete (cap := cap) x hx t)⟩
instance powerEdge_nonempty : Nonempty (PowerEdge (G := G) t cap) :=
  ⟨(fun _ => 0,PortGraph.Walk.ofWord (Classical.arbitrary V) (fun _ => Classical.arbitrary D))⟩
end PortCSP
end MetricKMedian.PCP

end Inline_PCPPowerCompleteness

end OAI
