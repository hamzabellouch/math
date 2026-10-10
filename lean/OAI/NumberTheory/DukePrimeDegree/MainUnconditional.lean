import OAI.NumberTheory.DukePrimeDegree.MainStarkDischarged
import OAI.NumberTheory.DukePrimeDegree.Entropy.RegularEntropyDischarge

namespace OAI

/-! # Prime-degree torus-packet equidistribution

The manuscript's full packet theorem, after discharging both the Stark
zero-exclusion input and the prime-degree positive-entropy rigidity input.
The lattice and field may vary, so nonmaximal multiplier orders and
arbitrary prescribed local homothety types are included. Tightness gives
no escape of mass for the complete volume-weighted packets.
-/

open MeasureTheory Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

universe u

/-- Theorem 1.1: complete volume-weighted packets converge to Haar
probability as their multiplier-order discriminants tend to infinity. -/
theorem prime_degree_packet_equidistribution_unconditional
    (d : ℕ) (hprime : Nat.Prime (d+1)) (hfive : 5 ≤ d+1)
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
  exact prime_degree_packet_equidistribution_of_EKL d hprime hfive
    (eklPrimeInput_unconditional d) K M σ hn hD

/-- The same packets converge to any specified Haar probability. -/
theorem prime_degree_packets_tendsto_haar_unconditional
    (d : ℕ) (hprime : Nat.Prime (d+1)) (hfive : 5 ≤ d+1)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, PrimeDegreePackets.FullLattice (d+1) (K i))
    (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i)=d+1)
    (hD : Tendsto (fun i => PrimeDegreePackets.multiplierDiscriminant (M i)) atTop atTop)
    (m : ProbabilityMeasure (X (d+1)))
    (hm : IsHaarProbability (m : Measure (X (d+1)))) :
    Tendsto (fun i => packetProbability (M i) (σ i) (hn i)
      (hprime.odd_of_ne_two (by omega))) atTop (𝓝 m) := by
  obtain ⟨ν,hν,hconv,_⟩ :=
    prime_degree_packet_equidistribution_unconditional d hprime hfive K M σ hn hD
  have heq : ν=m := Subtype.ext (isHaarProbability_unique hν hm)
  rwa [heq] at hconv

/-- Theorem 1.1 as weak convergence of the actual complete packet measures,
including tightness of the entire family. -/
theorem prime_degree_packet_measure_equidistribution_unconditional
    (d : ℕ) (hprime : Nat.Prime (d+1)) (hfive : 5 ≤ d+1)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, PrimeDegreePackets.FullLattice (d+1) (K i))
    (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i)=d+1)
    (hD : Tendsto (fun i => PrimeDegreePackets.multiplierDiscriminant (M i)) atTop atTop) :
    ∃ ν : Measure (X (d+1)), IsHaarProbability ν ∧
      WeakProbabilityConvergence (fun i => packetMeasure (M i) (σ i)) ν ∧
      IsTightMeasureSet (Set.range (fun i => packetMeasure (M i) (σ i))) := by
  obtain ⟨ν, hν, hconv, htight⟩ :=
    prime_degree_packet_equidistribution_unconditional d hprime hfive K M σ hn hD
  refine ⟨(ν : Measure (X (d+1))), hν, ?_, htight⟩
  exact (weakProbabilityConvergence_iff
    (fun i => packetProbability (M i) (σ i) (hn i)
      (hprime.odd_of_ne_two (by omega))) ν).mpr hconv

/-- The complete packet measures converge weakly to any specified Haar
probability, in the formulation by bounded continuous test functions. -/
theorem prime_degree_packet_measures_tendsto_haar_unconditional
    (d : ℕ) (hprime : Nat.Prime (d+1)) (hfive : 5 ≤ d+1)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, PrimeDegreePackets.FullLattice (d+1) (K i))
    (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i)=d+1)
    (hD : Tendsto (fun i => PrimeDegreePackets.multiplierDiscriminant (M i)) atTop atTop)
    (m : ProbabilityMeasure (X (d+1)))
    (hm : IsHaarProbability (m : Measure (X (d+1)))) :
    WeakProbabilityConvergence (fun i => packetMeasure (M i) (σ i))
      (m : Measure (X (d+1))) := by
  exact (weakProbabilityConvergence_iff
    (fun i => packetProbability (M i) (σ i) (hn i)
      (hprime.odd_of_ne_two (by omega))) m).mpr
    (prime_degree_packets_tendsto_haar_unconditional d hprime hfive K M σ hn hD m hm)

end DukePrimeDegree

end OAI
