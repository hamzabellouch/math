import Mathlib
import OAI.Analysis.WeakInfiniteness.SpectralResidual

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

section Unital

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A]

lemma exists_separated_spectral_windows
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (π : A →⋆ₐ[ℂ] B) {U p q : A} (hU : IsSelfAdjoint U) (hUD : U ∈ D)
    (hp : IsSelfAdjoint p) (hpD : p ∈ D) (hpq : p*q=0) (hc : π (p*U*q) ≠ 0) :
    ∃ u ∈ D,∃ v ∈ D,0 ≤ u ∧ 0 ≤ v ∧ u*v=0 ∧ π u ≠ 0 ∧ π v ≠ 0 ∧
      ∃ S T : Set ℝ,∃ ρ : ℝ,0 < ρ ∧ ContinuouslySupported U u S ∧
        ContinuouslySupported U v T ∧ (∀ x ∈ S,∀ y ∈ T,ρ ≤ dist x y) := by
  have hn : π U ≠ 0 := by
    intro hz
    apply hc
    rw [map_mul,map_mul,hz,mul_zero,zero_mul]
  obtain ⟨t,ht,ht0⟩ := exists_nonzero_spectral_value (hU.map π) hn
  by_cases htwo : ∃ s ∈ spectrum ℝ (π U),s ≠ 0 ∧ s ≠ t
  · obtain ⟨s,hs,hs0,hst⟩ := htwo
    exact exists_windows_of_two_nonzero_spectral_values D π hU hUD hs ht hs0 ht0 hst
  · apply exists_windows_of_single_nonzero_spectral_value D π hU hUD hp hpD hpq hc ht ht0
    intro s hs
    by_cases hs0 : s=0
    · exact Or.inl hs0
    · exact Or.inr (by by_contra hst; exact htwo ⟨s,hs,hs0,hst⟩)

end Unital

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type*} [CStarAlgebra B]

omit [PartialOrder A] [StarOrderedRing A] in
lemma starLift_inr_apply_general (π : A →⋆ₙₐ[ℂ] B) (a : A) :
    (Unitization.starLift π) (a : Unitization ℂ A)=π a :=
  congrArg (fun f : A →⋆ₙₐ[ℂ] B => f a) (Equiv.symm_apply_apply Unitization.starLift π)

omit [PartialOrder A] [StarOrderedRing A] in
lemma unitization_subalgebra_closed (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosed (D : Set A)) :
    IsClosed ((NonUnitalStarSubalgebra.map (Unitization.inrNonUnitalStarAlgHom ℂ A) D :
      NonUnitalStarSubalgebra ℂ (Unitization ℂ A)) : Set (Unitization ℂ A)) := by
  rw [NonUnitalStarSubalgebra.coe_map]
  exact Unitization.isometry_inr.isClosedEmbedding.isClosedMap _ hD

lemma exists_nonunital_separated_spectral_windows
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosed (D : Set A))
    (π : A →⋆ₙₐ[ℂ] B) {U p q : A} (hU : IsSelfAdjoint U) (hUD : U ∈ D)
    (hp : IsSelfAdjoint p) (hpD : p ∈ D) (hpq : p*q=0) (hc : π (p*U*q) ≠ 0) :
    ∃ u ∈ D,∃ v ∈ D,0 ≤ u ∧ 0 ≤ v ∧ u*v=0 ∧ π u ≠ 0 ∧ π v ≠ 0 ∧
      ∃ S T : Set ℝ,∃ ρ : ℝ,0 < ρ ∧
        ContinuouslySupported (U : Unitization ℂ A) (u : Unitization ℂ A) S ∧
        ContinuouslySupported (U : Unitization ℂ A) (v : Unitization ℂ A) T ∧
        (∀ x ∈ S,∀ y ∈ T,ρ ≤ dist x y) := by
  let ι := Unitization.inrNonUnitalStarAlgHom ℂ A
  let E := NonUnitalStarSubalgebra.map ι D
  let : IsClosed (E : Set (Unitization ℂ A)) := unitization_subalgebra_closed D hD
  have hEc : (Unitization.starLift π) (ι p*ι U*ι q) ≠ 0 := by
    rw [← map_mul,← map_mul]
    change (Unitization.starLift π) ((p*U*q : A) : Unitization ℂ A) ≠ 0
    rwa [starLift_inr_apply_general]
  obtain ⟨u,hu,v,hv,hu0,hv0,huv,hun,hvn,S,T,ρ,hρ,huS,hvT,hST⟩ :=
    exists_separated_spectral_windows E (Unitization.starLift π)
      (hU.map ι) (NonUnitalStarSubalgebra.mem_map.mpr ⟨U,hUD,rfl⟩)
      (hp.map ι) (NonUnitalStarSubalgebra.mem_map.mpr ⟨p,hpD,rfl⟩)
      (by rw [← map_mul,hpq,map_zero]) hEc
  obtain ⟨u₀,hu₀,rfl⟩ := NonUnitalStarSubalgebra.mem_map.mp hu
  obtain ⟨v₀,hv₀,rfl⟩ := NonUnitalStarSubalgebra.mem_map.mp hv
  refine ⟨u₀,hu₀,v₀,hv₀,Unitization.inr_nonneg_iff.mp hu0,
    Unitization.inr_nonneg_iff.mp hv0,?_,?_,?_,S,T,ρ,hρ,huS,hvT,hST⟩
  · apply Unitization.inr_injective (R := ℂ)
    change ι (u₀*v₀)=ι 0
    rw [map_mul,map_zero]
    exact huv
  · change (Unitization.starLift π) (u₀ : Unitization ℂ A) ≠ 0 at hun
    rwa [starLift_inr_apply_general] at hun
  · change (Unitization.starLift π) (v₀ : Unitization ℂ A) ≠ 0 at hvn
    rwa [starLift_inr_apply_general] at hvn

end NonUnital

end

end WeakPureInfiniteness
end

end OAI
