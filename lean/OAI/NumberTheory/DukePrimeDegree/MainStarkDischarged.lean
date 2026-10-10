import OAI.NumberTheory.DukePrimeDegree.Arithmetic.StarkUnconditional
import OAI.NumberTheory.DukePrimeDegree.MainReduction

namespace OAI

/-! # Packet equidistribution with Stark's input discharged

Arithmetic Artin reciprocity supplies the even ray realizations used in
exceptional-real-zero exclusion. Prime-degree positive-entropy rigidity
then implies convergence of complete packets and tightness.
-/

open MeasureTheory Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

universe u

theorem prime_degree_packet_equidistribution_of_EKL
    (d : ℕ) (hprime : Nat.Prime (d+1)) (hfive : 5 ≤ d+1)
    (ekl : EKLPrimeInput d)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, PrimeDegreePackets.FullLattice (d+1) (K i))
    (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i)=d+1)
    (hD : Tendsto (fun i => PrimeDegreePackets.multiplierDiscriminant (M i)) atTop atTop) :
    ∃ ν : ProbabilityMeasure (X (d+1)),
      IsHaarProbability (ν : Measure (X (d+1))) ∧
      Tendsto (fun i => packetProbability (M i) (σ i) (hn i)
        (hprime.odd_of_ne_two (by omega))) atTop (𝓝 ν) ∧
      IsTightMeasureSet (Set.range (fun i => packetMeasure (M i) (σ i))) := by
  exact prime_degree_packet_equidistribution_of_real_zero_exclusion d hprime hfive
    (exceptionalRealZeroExclusion_unconditional d (hprime.odd_of_ne_two (by omega)))
    ekl K M σ hn hD

end DukePrimeDegree

end OAI
