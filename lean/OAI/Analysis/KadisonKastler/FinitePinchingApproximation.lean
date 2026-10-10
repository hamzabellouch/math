import OAI.Analysis.KadisonKastler.UniformPinchingGap

namespace OAI

/-! # Finite subfamilies retain a strict pinching gap -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def finiteProjectionSubfamily (S : Set (AlgebraProjection M)) (F : Finset S) :
    Set (AlgebraProjection M) := Subtype.val '' (F : Set S)

theorem finiteProjectionSubfamily_subset (S : Set (AlgebraProjection M)) (F : Finset S) :
    finiteProjectionSubfamily S F ⊆ S := by
  rintro _ ⟨p,_,rfl⟩
  exact p.property

theorem finiteProjectionSubfamily_union (S : Set (AlgebraProjection M)) :
    (⋃ F : Finset S, finiteProjectionSubfamily S F)=S := by
  classical
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (finiteProjectionSubfamily_subset S)
  · intro p hp
    apply Set.mem_iUnion.mpr
    exact ⟨{⟨p,hp⟩},⟨⟨p,hp⟩,by simp,rfl⟩⟩

theorem finiteProjectionSubfamily_monotone (S : Set (AlgebraProjection M)) :
    Monotone (finiteProjectionSubfamily S) := by
  intro F G hFG
  exact Set.image_mono hFG

theorem finite_pinching_tendsto (J : H ≃ₗᵢ⋆[ℂ] H) (S : Set (AlgebraProjection M)) (x : H) :
    Tendsto (fun F : Finset S => projectionFamilyPinching J (finiteProjectionSubfamily S F) x)
      atTop (𝓝 (projectionFamilyPinching J S x)) := by
  have ht := projectionFamilyPinching_tendsto J _ (finiteProjectionSubfamily_monotone S) x
  rwa [finiteProjectionSubfamily_union] at ht

theorem exists_finite_pinching_gap (J : H ≃ₗᵢ⋆[ℂ] H) (S : Set (AlgebraProjection M))
    (ξ η : H) (δ g : ℝ)
    (hgap : g < ‖(1-projectionFamilyPinching J S) η‖^2)
    (hstrict : ‖(1-projectionFamilyPinching J S) ξ‖^2 <
      δ*‖(1-projectionFamilyPinching J S) η‖^2) :
    ∃ T : Set (AlgebraProjection M), T.Finite ∧ T⊆S ∧
      g < ‖(1-projectionFamilyPinching J T) η‖^2 ∧
      ‖(1-projectionFamilyPinching J T) ξ‖^2 < δ*‖(1-projectionFamilyPinching J T) η‖^2 := by
  classical
  have he (z : H) : Tendsto
      (fun F : Finset S => ‖(1-projectionFamilyPinching J (finiteProjectionSubfamily S F)) z‖^2)
      atTop (𝓝 (‖(1-projectionFamilyPinching J S) z‖^2)) := by
    have hc : Tendsto (fun _ : Finset S => z) atTop (𝓝 z) := tendsto_const_nhds
    simpa only [sub_apply,one_apply_eq_self] using (hc.sub (finite_pinching_tendsto J S z)).norm.pow 2
  have h1 := (he η).eventually (eventually_gt_nhds hgap)
  have h2 := (((he η).const_mul δ).sub (he ξ)).eventually
    (eventually_gt_nhds (sub_pos.mpr hstrict))
  obtain ⟨F,hF1,hF2⟩ := (h1.and h2).exists
  refine ⟨finiteProjectionSubfamily S F,(F.finite_toSet).image _,
    finiteProjectionSubfamily_subset S F,hF1,?_⟩
  exact sub_pos.mp hF2

variable [TopologicalSpace.SeparableSpace H]

local instance finitePinchingRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

theorem exists_finite_uniform_pinching_gap
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (η : H) (hη : J η=η) (huη : ‖η‖=1) (horth : inner ℂ ξ η=0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ T : Set (AlgebraProjection M), T.Finite ∧ (∀ p∈T, p.val≠0) ∧
      T.Pairwise (fun p q => p.val*q.val=0) ∧
      1/16 < 131072*‖(1-projectionFamilyPinching J T) η‖^2 ∧
      ‖(1-projectionFamilyPinching J T) ξ‖^2 < δ*‖(1-projectionFamilyPinching J T) η‖^2 := by
  obtain ⟨S,hS,hgap⟩ := exists_uniform_pinching_gap J hJ hright hleft ξ hξ huξ hsep hpos
    hIII hremote η hη huη horth (δ/2) (half_pos hδ)
  have hposgap : 0 < ‖(1-projectionFamilyPinching J S) η‖^2 := by linarith only [hgap]
  have hg : (1:ℝ)/2097152 < ‖(1-projectionFamilyPinching J S) η‖^2 := by linarith only [hgap]
  have hs : ‖(1-projectionFamilyPinching J S) ξ‖^2 <
      δ*‖(1-projectionFamilyPinching J S) η‖^2 := by
    have hh := hS.2.2.2
    have hdg := mul_pos hδ hposgap
    nlinarith only [hh,hdg]
  obtain ⟨T,hT,hTS,hTgap,hTsmall⟩ := exists_finite_pinching_gap J S ξ η δ
    (1/2097152) hg hs
  refine ⟨T,hT,fun p hp => hS.1 p (hTS hp),hS.2.1.mono hTS,?_,hTsmall⟩
  linarith only [hTgap]

end

end KadisonKastler

end OAI
