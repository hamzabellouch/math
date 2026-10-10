import OAI.Analysis.KadisonKastler.ProjectionFamilyAdmissible
import OAI.Analysis.KadisonKastler.ProjectionFamilyPinchingInsert

namespace OAI

/-! # Maximal admissible orthogonal projection families

Chain unions retain the two quantitative inequalities by strong convergence
of the constructed kernel projections.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def AdmissibleOrthogonalFamily (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) (δ : ℝ)
    (S : Set (AlgebraProjection M)) : Prop :=
  (∀ p ∈ S, p.val≠0) ∧ S.Pairwise (fun p q => p.val*q.val=0) ∧
    ProjectionFamilyAdmissible J ξ η δ S

theorem projectionFamilyRemainder_empty :
    (projectionFamilyRemainder (∅ : Set (AlgebraProjection M))).val=1 := by
  apply Subtype.ext
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  change x ∈ projectionFamilyRemainderSpace (∅ : Set (AlgebraProjection M))
  rw [mem_projectionFamilyRemainderSpace]
  simp

theorem projectionFamilyPinching_empty (J : H ≃ₗᵢ⋆[ℂ] H) :
    projectionFamilyPinching J (∅ : Set (AlgebraProjection M))=1 := by
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  change x ∈ projectionFamilyCommutationSpace J (∅ : Set (AlgebraProjection M))
  rw [mem_projectionFamilyCommutationSpace]
  simp

theorem admissibleOrthogonalFamily_empty (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ η : H) (δ : ℝ) : AdmissibleOrthogonalFamily (M := M) J ξ η δ ∅ := by
  refine ⟨by simp,by simp,?_⟩
  unfold ProjectionFamilyAdmissible
  rw [projectionFamilyRemainder_empty,modularQuadratic_one J hJ,projectionFamilyPinching_empty]
  simp

theorem exists_maximal_admissibleOrthogonalFamily
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (ξ η : H) (δ : ℝ) :
    ∃ S : Set (AlgebraProjection M), Maximal (AdmissibleOrthogonalFamily J ξ η δ) S := by
  apply zorn_subset
  intro C hC hc
  by_cases hne : C.Nonempty
  · let : Nonempty C := hne.to_subtype
    let : IsDirected C (·≤·) := ⟨by
      intro a b
      rcases hc.total a.property b.property with hab | hba
      · exact ⟨b,hab,le_rfl⟩
      · exact ⟨a,le_rfl,hba⟩⟩
    have hAdm : ProjectionFamilyAdmissible J ξ η δ (⋃₀ C) := by
      have hh := projectionFamilyAdmissible_iUnion J ξ η δ (fun i : C => i.val)
        (fun _ _ hij => hij) (fun i => (hC i.property).2.2)
      have he : (⋃ i : C, i.val)=⋃₀ C := by ext p; simp
      rwa [he] at hh
    refine ⟨⋃₀ C,⟨?_,?_,hAdm⟩,fun S hS => Set.subset_sUnion_of_mem hS⟩
    · rintro p ⟨S,hS,hp⟩
      exact (hC hS).1 p hp
    · rintro p ⟨S,hS,hp⟩ q ⟨T,hT,hq⟩ hpq
      rcases hc.total hS hT with hST | hTS
      · exact (hC hT).2.1 (hST hp) hq hpq
      · exact (hC hS).2.1 hp (hTS hq) hpq
  · refine ⟨∅,admissibleOrthogonalFamily_empty J hJ ξ η δ,?_⟩
    intro S hS
    exact False.elim (hne ⟨S,hS⟩)

end

end KadisonKastler

end OAI
