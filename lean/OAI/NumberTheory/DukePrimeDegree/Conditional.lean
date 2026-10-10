import OAI.NumberTheory.DukePrimeDegree.Arithmetic.PublishedStark
import OAI.NumberTheory.DukePrimeDegree.MainConditional

namespace OAI

/-!
# Theorem 1.1 conditional on published inputs

This is the manuscript's main result for arbitrary full-lattice local
types, including varying number fields and nonmaximal multiplier orders.
The only explicit inputs are `StarkInput` (Stark 1974, Lemmas 3 and 8 and
equation (9)) and `EKLPrimeInput` (EKL 2006, Theorem 1.3/Corollary 1.4).
The intermediate uniform zeta estimate is derived, not assumed.
-/

open MeasureTheory Filter
open scoped Topology

namespace DukePrimeDegree

open PrimeDegreePackets

universe u

/-- Conditional form of Theorem 1.1, including tightness of the entire
sequence of complete volume-weighted local-homothety packets. -/
theorem prime_degree_packet_equidistribution
    (d : ℕ) (hprime : Nat.Prime (d + 1)) (hfive : 5 ≤ d + 1)
    (stark : StarkInput.{u} (d + 1)) (ekl : EKLPrimeInput d)
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
    (uniformZetaScaleBound_of_stark hprime (by omega) stark) ekl K M σ hn hD

/-- The same sequence converges to the distinguished invariant
probability, whenever it is presented explicitly. -/
theorem tendsto_haar_of_published_inputs
    (d : ℕ) (hprime : Nat.Prime (d + 1)) (hfive : 5 ≤ d + 1)
    (stark : StarkInput.{u} (d + 1)) (ekl : EKLPrimeInput d)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, PrimeDegreePackets.FullLattice (d + 1) (K i))
    (σ : ∀ i, OrderedEmbeddings (d + 1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d + 1)
    (hD : Tendsto (fun i => PrimeDegreePackets.multiplierDiscriminant (M i)) atTop atTop)
    (m : ProbabilityMeasure (X (d + 1))) (hm : IsHaarProbability (m : Measure (X (d + 1)))) :
    Tendsto (fun i => packetProbability (M i) (σ i) (hn i)
      (hprime.odd_of_ne_two (by omega))) atTop (𝓝 m) := by
  obtain ⟨ν, hν, hconv, _⟩ :=
    prime_degree_packet_equidistribution d hprime hfive stark ekl K M σ hn hD
  have heq : ν = m := Subtype.ext (isHaarProbability_unique hν hm)
  rwa [heq] at hconv

end DukePrimeDegree

end OAI
