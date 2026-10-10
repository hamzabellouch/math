import OAI.Analysis.KadisonKastler.RegularCoreEigenoperator
import OAI.Analysis.KadisonKastler.RegularSpatialField

namespace OAI

/-! # Factoriality of the core from two site frequencies

This is the fixed tensor-factor argument of the manuscript. Its product
hypotheses concern local swaps and two explicit site eigenoperators.
These hypotheses imply factoriality of the crossed product.
-/

namespace KadisonKastler

open MeasureTheory UnitalTomsWinter

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace H]
  [TopologicalSpace.SeparableSpace (SpatialHilbert H K)]

/-- Independent product swaps and two incommensurable site frequencies
force the actual regular crossed product of a tensor factor to be a factor. -/
theorem scalarCenter_regularCore_of_two_site_frequencies
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (M : VonNeumannAlgebra H) (hM : ScalarCenter M)
    (D : VonNeumannAlgebra K) (Ω : K) (hΩ : ‖Ω‖ = 1)
    (L : LocalProductSwaps D Ω)
    (hsep : Function.Injective (algebraVectorMap D Ω))
    (U : Multiplicative ℝ →* unitary (SpatialHilbert H K →L[ℂ] SpatialHilbert H K))
    (hU : ∀ ξ, Continuous (fun t : ℝ =>
      (U (Multiplicative.ofAdd t) : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) ξ))
    (hP : ∀ s x, x ∈ spatialProductAlgebra M D →
      unitaryConj (U s) x ∈ spatialProductAlgebra M D)
    (hfixed : ∀ u : unitary (K →L[ℂ] K), (u : K →L[ℂ] K) ∈ D →
      ProductStateCentralizes D Ω u → ∀ s,
      unitaryConj (U s) (spatialRight (H := H) (u : K →L[ℂ] K)) =
        spatialRight (H := H) (u : K →L[ℂ] K))
    (b₁ b₂ : K →L[ℂ] K) (hb₁ : b₁ ∈ D) (hb₂ : b₂ ∈ D)
    (hn₁ : b₁ ≠ 0) (hn₂ : b₂ ≠ 0) (s₁ s₂ : ℝ) (hirr : Irrational (s₁ / s₂))
    (heigen₁ : ∀ t : ℝ,
      unitaryConj (star (U (Multiplicative.ofAdd t))) (spatialRight (H := H) b₁) =
        regularCharacterScalar (2 * Real.pi * s₁) t • spatialRight (H := H) b₁)
    (heigen₂ : ∀ t : ℝ,
      unitaryConj (star (U (Multiplicative.ofAdd t))) (spatialRight (H := H) b₂) =
        regularCharacterScalar (2 * Real.pi * s₂) t • spatialRight (H := H) b₂) :
    ScalarCenter (regularCoreAlgebra U hU (spatialProductAlgebra M D)) := by
  let P := spatialProductAlgebra M D
  let Φ := (Lp.fourierTransformₗᵢ ℝ (SpatialHilbert H K)).conjStarAlgEquiv
  intro T hT hcentral
  obtain ⟨F, hFm, hFn, _, hFT⟩ := regularCore_central_fourier_field U hU P
    hSpectral hDiagonal hP T hT hcentral
  have htensor : Φ T ∈ regularTensorAlgebra P := by
    apply (mem_regularTensorAlgebra_iff P _).mpr
    intro b hb
    have he := congrArg Φ ((mem_regularTensorAlgebra_iff P T).mp
      (regularCoreAlgebra_le_tensor U hU P hP hT) b hb)
    simpa only [map_mul, Φ, fourierConj_regularConstantHom] using he
  have hcomm : ∀ u : unitary (K →L[ℂ] K), (u : K →L[ℂ] K) ∈ D →
      ProductStateCentralizes D Ω u → Commute (Φ T)
        (regularConstantHom volume (spatialRight (H := H) (u : K →L[ℂ] K))) := by
    intro u hu hc
    exact regularCore_central_fourier_commutes_fixed U hU P T hcentral _
      (spatialRight_mem_product M D hu) (hfixed u hu hc)
  obtain ⟨A, hAm, hAn, _, hAT⟩ := first_leg_field_of_product_centralizer M L hΩ hsep
    F (Φ T) hFT hFm ‖T‖ hFn htensor hcomm
  have hEigenComm (b : K →L[ℂ] K) (hb : b ∈ D) (s : ℝ)
      (heigen : ∀ t : ℝ,
        unitaryConj (star (U (Multiplicative.ofAdd t))) (spatialRight (H := H) b) =
          regularCharacterScalar (2 * Real.pi * s) t • spatialRight (H := H) b) :
      Commute (Φ T) (regularConstantHom volume (spatialRight (H := H) b) *
        (regularRightTranslation (H := SpatialHilbert H K) (Multiplicative.ofAdd (-s)) :
          RegularCoreHilbert (SpatialHilbert H K) →L[ℂ]
            RegularCoreHilbert (SpatialHilbert H K))) := by
    have he := congrArg Φ (hcentral _ (regularCoreEmbedding_mem_core U hU P
      (spatialRight_mem_product M D hb)))
    simp only [map_mul] at he
    rw [show Φ (regularCoreEmbedding U hU (spatialRight (H := H) b)) = _ from
      fourierConj_regularCoreEigenoperator U hU _ s heigen] at he
    exact he.symm
  have hirr' : Irrational ((-s₁) / (-s₂)) := by simpa only [neg_div_neg_eq] using hirr
  obtain ⟨a, _, hconst⟩ := spatialField_constant_of_two_shifts hAT hAm ‖T‖ hAn
    b₁ b₂ hn₁ hn₂ (-s₁) (-s₂) hirr' (by
      rintro b s (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hEigenComm b hb₁ s₁ heigen₁
      · exact hEigenComm b hb₂ s₂ heigen₂)
  have hTconst : T = regularConstantHom volume (spatialLeft (K := K) a) := by
    have he : Φ T = Φ (regularConstantHom volume (spatialLeft (K := K) a)) :=
      hconst.trans (fourierConj_regularConstantHom _).symm
    exact Φ.injective he
  rw [hTconst] at hT hcentral ⊢
  exact regularCore_constant_central_scalar U hU P hP
    (scalarCenter_spatialProduct_of_local_swaps M hM L hΩ hsep) _ hT hcentral

end

end KadisonKastler

end OAI
