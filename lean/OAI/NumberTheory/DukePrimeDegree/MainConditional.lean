import OAI.NumberTheory.PrimePackets.ZetaDerivatives
import OAI.NumberTheory.DukePrimeDegree.Geometry.Convergence

namespace OAI

/-!
# Conditional prime-degree packet equidistribution

Complete volume-weighted local-homothety packets converge to Haar
probability and form a tight family under a residue-relative uniform
zeta scale bound and prime-degree positive-entropy rigidity. The
arithmetic and dynamical hypotheses concern the actual homogeneous
lattice space and its diagonal action. A subsequential packet limit
supplies Haar probability.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree

open PrimeDegreePackets

universe u

/-- The published rigidity input, on the actual lattice space and with
actual diagonal ergodicity and measure-theoretic entropy. -/
def EKLPrimeInput (d : ℕ) : Prop :=
  Nat.Prime (d + 1) → 3 ≤ d + 1 →
    ∀ ν : Measure (X (d + 1)), IsProbabilityMeasure ν →
      ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) ν →
      0 < measureEntropy ν
        (fun x => rightAction x (diagonalOneParameter (regularDiagonalWeights d)
          (regularDiagonalWeights_sum d) 1)) → IsHaarProbability ν

/-- Every weak packet limit is Haar under the analytic scale bound and
published prime-degree rigidity. -/
theorem packet_limit_isHaar_of_scale_and_EKL
    (d : ℕ) (hprime : Nat.Prime (d + 1)) (hthree : 3 ≤ d + 1) (hodd : Odd (d + 1))
    (Hscale : UniformZetaScaleBound.{u} (d + 1)) (ekl : EKLPrimeInput d)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, PrimeDegreePackets.FullLattice (d + 1) (K i))
    (σ : ∀ i, OrderedEmbeddings (d + 1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d + 1)
    (hD : Tendsto (fun i => PrimeDegreePackets.multiplierDiscriminant (M i)) atTop atTop)
    (ν : ProbabilityMeasure (X (d + 1)))
    (hlim : Tendsto (fun i => packetProbability (M i) (σ i) (hn i) hodd)
      atTop (𝓝 ν)) : IsHaarProbability (ν : Measure (X (d + 1))) := by
  obtain ⟨m, hm, hdec, hcomp⟩ :=
    packet_limit_positive_ergodic_components_of_zeta_scale d hodd Hscale K M σ hn hD ν hlim
  let : MeasurableSpace (X (d + 1)) := xMeasurableSpace (d + 1)
  let : @IsProbabilityMeasure (X (d + 1)) m
      ((ν : Measure (X (d + 1))).trim hm) := by
    constructor
    rw [trim_measurableSet_eq hm (@MeasurableSet.univ _ m)]
    exact measure_univ
  have hHaar : ∀ᵐ z ∂(ν : Measure (X (d + 1))).trim hm,
      IsHaarProbability (condExpKernel (ν : Measure (X (d + 1))) m z) := by
    filter_upwards [hcomp] with z hz
    exact ekl hprime hthree _ inferInstance hz.1 hz.2
  obtain ⟨z, hz⟩ := hHaar.exists
  have heq := measure_eq_haar_of_condExpKernel_invariance
    (ν : Measure (X (d + 1)))
    (condExpKernel (ν : Measure (X (d + 1))) m z) hz m hm hdec
    (hHaar.mono fun _ h => h.2)
  exact heq.symm ▸ hz

/-- The full volume-weighted packet conclusion, including no escape of
mass, conditional on the explicitly separated analytic and published
rigidity inputs. The family may vary through arbitrary full lattices and
arbitrary local homothety types. -/
theorem prime_degree_packet_equidistribution_of_scale_and_EKL
    (d : ℕ) (hprime : Nat.Prime (d + 1)) (hfive : 5 ≤ d + 1)
    (Hscale : UniformZetaScaleBound.{u} (d + 1)) (ekl : EKLPrimeInput d)
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
  let hodd : Odd (d + 1) := hprime.odd_of_ne_two (by omega)
  let p : ℕ → ProbabilityMeasure (X (d + 1)) :=
    fun i => packetProbability (M i) (σ i) (hn i) hodd
  have hQ := packetScale_tendsto_of_multiplierDiscriminant_tendsto
    (Nat.succ_pos d) K M hn hD
  have htight := packet_tight_of_zeta_scale d hodd Hscale K M σ hn hQ
  obtain ⟨ν, φ, hφ, hsub⟩ :=
    packet_probability_subsequence_of_zeta_scale d hodd Hscale K M σ hn hD
  have hHaar := packet_limit_isHaar_of_scale_and_EKL d hprime (by omega) hodd Hscale ekl
    (fun i => K (φ i)) (fun i => M (φ i)) (fun i => σ (φ i))
    (fun i => hn (φ i)) (hD.comp hφ.tendsto_atTop) ν hsub
  refine ⟨ν, hHaar, ?_, htight⟩
  have htight' : IsTightMeasureSet {μ : Measure (X (d + 1)) | ∃ i, μ = p i} := by
    convert htight using 1
    ext μ
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor <;> rintro ⟨i, hi⟩ <;> exact ⟨i, hi.symm⟩
  apply tendsto_of_tight_of_unique_subsequential_limit p ν htight'
  intro ψ hψ ξ hξ
  have hHaarξ := packet_limit_isHaar_of_scale_and_EKL d hprime (by omega) hodd Hscale ekl
    (fun i => K (ψ i)) (fun i => M (ψ i)) (fun i => σ (ψ i))
    (fun i => hn (ψ i)) (hD.comp hψ.tendsto_atTop) ξ hξ
  exact Subtype.ext (isHaarProbability_unique hHaarξ hHaar)

end DukePrimeDegree

end OAI
