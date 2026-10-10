import Mathlib
import OAI.RepresentationTheory.PartialPermutation.ProjectionCovers
import OAI.RepresentationTheory.PartialPermutation.JointKernels

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation
noncomputable section
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {b : ℕ} (H : Fin b → Subgroup G)

lemma joint_small_type_cover (hb : 0 < b) (hD : 0 < Module.finrank ℂ V)
    (hρ : IsUnitary ρ)
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ H i, ∀ k ∈ H j, Commute g k)
    (c : isotypicComponents ℂ[↥(⨆ i, H i)] (Representation.asModule (ρ.comp (⨆ i, H i).subtype))) :
    ∃ i, ∀ x ∈ componentSpace (ρ.comp (⨆ i, H i).subtype) c,
      complexFourier (ρ.comp (H i).subtype)
        (smallTypeKernel (H i) ((Module.finrank ℂ V : ℝ)^(1 / (b : ℝ)))) x = x := by
  let J := ⨆ i, H i
  let ρJ : Representation ℂ J V := ρ.comp J.subtype
  obtain ⟨i, d, k, hd, hk, hki, hka⟩ := component_kernel ρ H hb hD hρ hcomm c
  let σ : Subrepresentation (ρ.comp (H i).subtype) :=
    { toSubmodule := componentSpace ρJ c
      apply_mem_toSubmodule := fun g v hv =>
        componentSpace_invariant ρJ c ⟨g, le_iSup H i g.property⟩ v hv }
  have hu : IsUnitary σ.toRepresentation := fun g x y => hρ g x y
  have ha : complexFourier σ.toRepresentation k = 1 := by
    ext x
    rw [complexFourier_subrep]
    exact hka x.val x.property
  have hs := smallTypeKernel_identity_of_kernel σ.toRepresentation hu k d
    ((Module.finrank ℂ V : ℝ)^(1 / (b : ℝ))) hd hk ha
  refine ⟨i, fun x hx => ?_⟩
  have ht := congrArg (fun A : Module.End ℂ σ.toSubmodule => A ⟨x, hx⟩) hs
  have ht' := congrArg (fun y : σ.toSubmodule => (y : V)) ht
  rw [complexFourier_subrep] at ht'
  exact ht'

theorem small_degree_sum_transfer [Representation.IsIrreducible ρ]
    (hb : 0 < b) (hρ : IsUnitary ρ)
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ H i, ∀ k ∈ H j, Commute g k)
    (f : G → ℝ) (B : ℝ) (hf : ∀ g, 0 ≤ f g) (hcap : ∀ i, LeftCosetCap f (H i) B) :
    (Module.finrank ℂ V : ℝ) * hsNormSq (complexFourier ρ (fun g => f g)) ≤
      B * mass f * ∑ i, smallDegreeSum (H i) ((Module.finrank ℂ V : ℝ)^(1 / (b : ℝ))) := by
  have : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  have hD : 0 < Module.finrank ℂ V := Module.finrank_pos
  let R := (Module.finrank ℂ V : ℝ)^(1 / (b : ℝ))
  let P (i : Fin b) := complexFourier (ρ.comp (H i).subtype) (smallTypeKernel (H i) R)
  have hp (i : Fin b) : LinearMap.adjoint (P i) = P i :=
    complexFourier_selfAdjoint (G := H i) (ρ.comp (H i).subtype)
      (fun (g : H i) => hρ g) _ (smallTypeKernel_inv R)
  have hcover := component_projection_cover_hs (G := ↥(⨆ i, H i))
    (ρ.comp (⨆ i, H i).subtype) (fun (g : ↥(⨆ i, H i)) => hρ g) P hp
    (joint_small_type_cover ρ H hb hD hρ hcomm) (complexFourier ρ (fun g => f g))
  calc
    _ ≤ (Module.finrank ℂ V : ℝ) * ∑ i, hsNormSq (complexFourier ρ (fun g => f g) * P i) :=
      mul_le_mul_of_nonneg_left hcover (by positivity)
    _ = ∑ i, (Module.finrank ℂ V : ℝ) * hsNormSq (complexFourier ρ (fun g => f g) * P i) :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ i, B * mass f * smallDegreeSum (H i) R :=
      Finset.sum_le_sum (fun i _ => small_type_hs_bound ρ hρ (H i) R f B hf (hcap i))
    _ = _ := by rw [Finset.mul_sum]

end
end PartialPermutation

end

end OAI
