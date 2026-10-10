import OAI.NumberTheory.DukePrimeDegree.Arithmetic.StarkZeros
import OAI.NumberTheory.DukePrimeDegree.MainConditional

namespace OAI

/-!
# Packet equidistribution from exceptional-zero exclusion

Completed-zeta continuation, the zero sum and complex zero separation
reduce the analytic hypothesis to real exceptional-zero exclusion.
Together with prime-degree positive-entropy rigidity, this gives
convergence of complete packets and tightness.
-/

open MeasureTheory Filter
open scoped Topology

namespace DukePrimeDegree

open PrimeDegreePackets

universe u

/-- Theorem 1.1 with all of Stark's analytic ingredients discharged.
Only real exceptional-zero exclusion and measure rigidity remain. -/
theorem prime_degree_packet_equidistribution_of_real_zero_exclusion
    (d : ℕ) (hprime : Nat.Prime (d + 1)) (hfive : 5 ≤ d + 1)
    (stark : ExceptionalRealZeroExclusion.{u} d) (ekl : EKLPrimeInput d)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, PrimeDegreePackets.FullLattice (d + 1) (K i))
    (σ : ∀ i, OrderedEmbeddings (d + 1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d + 1)
    (hD : Tendsto (fun i => PrimeDegreePackets.multiplierDiscriminant (M i)) atTop atTop) :
    ∃ ν : ProbabilityMeasure (X (d + 1)),
      IsHaarProbability (ν : Measure (X (d + 1))) ∧
      Tendsto (fun i => packetProbability (M i) (σ i) (hn i)
        (hprime.odd_of_ne_two (by omega))) atTop (𝓝 ν) ∧
      IsTightMeasureSet (Set.range (fun i => packetMeasure (M i) (σ i))) := by
  exact prime_degree_packet_equidistribution_of_scale_and_EKL d hprime hfive
    (uniformZetaScaleBound_of_completedXiGap d
      (completedXiGap_of_exceptionalRealZeroExclusion d stark)) ekl K M σ hn hD

end DukePrimeDegree

end OAI
