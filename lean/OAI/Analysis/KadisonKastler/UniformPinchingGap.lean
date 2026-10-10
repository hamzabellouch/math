import OAI.Analysis.KadisonKastler.ProjectionFamilyMaximal

namespace OAI

/-! # A uniform test-vector gap for an admissible projection family

A maximal admissible family cannot have a small gap: its remaining corner
would admit the strict refinement already constructed. This is the
projection-family amplification of the local Haagerup witness.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance uniformPinchingRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

theorem maximal_admissibleFamily_gap
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (η : H) (hη : J η=η) (huη : ‖η‖=1) (horth : inner ℂ ξ η=0)
    (δ : ℝ) (hδ : 0 < δ) (S : Set (AlgebraProjection M))
    (hS : Maximal (AdmissibleOrthogonalFamily J ξ η δ) S) :
    1/16 < 131072*‖(1-projectionFamilyPinching J S) η‖^2 := by
  by_contra hn
  have hgap := le_of_not_gt hn
  let q := projectionFamilyRemainder S
  let A := projectionFamilySelectedPart J S
  have hR : A+modularQuadratic J q.val=projectionFamilyPinching J S := by
    dsimp only [A,projectionFamilySelectedPart,q]
    abel
  obtain ⟨p,hp,hpq,_hproj,hwide,hsmall,hstrict⟩ := exists_strict_pinching_refinement
    J hJ hright hleft ξ hξ huξ hsep hpos hIII hremote η hη huη horth
    A (projectionFamilySelectedPart_isProjection J hJ hright S) q
    (projectionFamilySelectedPart_orthogonal J hJ hright S) δ hδ
    (by rw [hR]; exact hS.prop.2.2.1)
    (by rw [hR]; exact hS.prop.2.2.2) (by rwa [hR])
  have hnew : AdmissibleOrthogonalFamily J ξ η δ (insert p S) := by
    refine ⟨?_,?_,?_⟩
    · intro r hr
      rcases hr with rfl | hr
      · exact hp
      · exact hS.prop.1 r hr
    · apply hS.prop.2.1.insert
      intro r hr _
      have hrq : r.val*q.val=0 := Subtype.ext (projectionFamily_left_annihilate S r hr)
      have hpq' : q.val*p.val=p.val := hpq
      have hrp : r.val*p.val=0 := by
        calc
          _ = r.val*(q.val*p.val) := by rw [hpq']
          _ = 0 := by rw [← mul_assoc,hrq,zero_mul]
      have hpr : p.val*r.val=0 := by
        have he := congrArg star hrp
        simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
          r.property.isSelfAdjoint.star_eq,star_zero] using he
      exact ⟨hpr,hrp⟩
    · unfold ProjectionFamilyAdmissible
      rw [projectionFamilyRemainder_insert S p hpq,
        projectionFamilyPinching_insert J hJ hright S p hpq]
      exact ⟨hwide,hsmall⟩
  have heq : insert p S=S := Set.Subset.antisymm (hS.2 hnew (Set.subset_insert p S))
    (Set.subset_insert p S)
  have heR := projectionFamilyPinching_insert J hJ hright S p hpq
  rw [heq] at heR
  rw [hR,← heR] at hstrict
  exact (lt_irrefl _) hstrict

theorem exists_uniform_pinching_gap
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (η : H) (hη : J η=η) (huη : ‖η‖=1) (horth : inner ℂ ξ η=0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ S : Set (AlgebraProjection M), AdmissibleOrthogonalFamily J ξ η δ S ∧
      1/16 < 131072*‖(1-projectionFamilyPinching J S) η‖^2 := by
  obtain ⟨S,hS⟩ := exists_maximal_admissibleOrthogonalFamily (M := M) J hJ ξ η δ
  exact ⟨S,hS.prop,maximal_admissibleFamily_gap J hJ hright hleft ξ hξ huξ hsep hpos
    hIII hremote η hη huη horth δ hδ S hS⟩

end

end KadisonKastler

end OAI
