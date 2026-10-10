import Mathlib
import OAI.Analysis.Commutator.CStarContractiveLifts
import OAI.Analysis.Commutator.TracialSequenceCompression
import OAI.Analysis.Commutator.TracialSequenceTrace
import OAI.Analysis.Commutator.TracialUltrapower

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤atTop)

include hτ hω in
theorem bicommutant_norm_lift {T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω)))) :
    ∃ a : ℕ →ᵇ A, ‖a‖≤‖T‖ ∧ leftRestricted τ ω a=T := by
  rw [range_bicommutant τ ω hτ hω] at hT
  exact CStarContractiveLifts.operator_norm_lift (leftRestricted τ ω) hT

include hτ hω in
theorem bicommutant_trace_mul
    {S T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hS : S∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω)))) :
    sequenceTrace τ ω (S*T)=sequenceTrace τ ω (T*S) := by
  rw [range_bicommutant τ ω hτ hω] at hS hT
  obtain ⟨a,rfl⟩ := hS
  obtain ⟨b,rfl⟩ := hT
  simpa only [map_mul] using trace_mul τ ω hτ a b

include hτ hω in
theorem bicommutant_commutator_bound (S : τ.GNS →L[ℂ] τ.GNS) (c : ℝ)
    (hc : 0≤c)
    (hS : ∀ a : A, ‖S*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*S‖≤c*‖a‖)
    {T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω)))) :
    ‖compressed τ ω S*T-T*compressed τ ω S‖≤c*‖T‖ := by
  obtain ⟨a,hna,rfl⟩ := bicommutant_norm_lift τ ω hτ hω hT
  apply commutator_bound τ ω S a (c*‖leftRestricted τ ω a‖)
  intro i
  exact (hS (a i)).trans (mul_le_mul_of_nonneg_left ((a.norm_coe_le_norm i).trans hna) hc)

end Kadison.TracialSequence

end

end
end

end OAI
