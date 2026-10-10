import OAI.Analysis.KadisonKastler.BilateralBlockFunctions
import OAI.Analysis.KadisonKastler.IndependentUnitaryVariance

namespace OAI

/-! The quantitative independent-block estimate for the bilateral cocycle. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {G K : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

theorem bilateralBlock_collapse (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G)) :
    countableUnitaryL2 σ (bilateralRightWord_measurable G m)
      (countableUnitaryL2 σ (bilateralMiddleWord_measurable G m) (bilateralBlockA σ m g)) =
    countableUnitaryL2 σ (bilateralIncrementProduct_measurable G (2 * m + 2)) g := by
  apply Lp.ext
  have hA := countableUnitaryL2_ae σ (bilateralLeftWord_measurable G m) g
  filter_upwards [countableUnitaryL2_ae σ (bilateralRightWord_measurable G m)
    (countableUnitaryL2 σ (bilateralMiddleWord_measurable G m) (bilateralBlockA σ m g)),
    countableUnitaryL2_ae σ (bilateralMiddleWord_measurable G m) (bilateralBlockA σ m g),
    hA, countableUnitaryL2_ae σ (bilateralIncrementProduct_measurable G (2 * m + 2)) g]
      with ω hR hP hQ hW
  rw [hR, hP]
  change _ = _ at hQ
  change _ = (σ _ : K →L[ℂ] K) (g ω) at hW
  change (bilateralBlockA σ m g) ω = (σ _ : K →L[ℂ] K) (g ω) at hQ
  rw [hQ, hW, bilateral_block_word_factorization, map_mul, map_mul]
  rfl

theorem bilateralBlock_error (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (f g : Lp K 2 (bilateralWalkLaw G))
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω)) :
    ‖countableUnitaryL2 σ (bilateralMiddleWord_measurable G m) (bilateralBlockA σ m g) -
      bilateralBlockB σ m g‖ ≤ 2 * ‖f - g‖ := by
  have hB : countableUnitaryL2 σ (bilateralRightWord_measurable G m) (bilateralBlockB σ m g) =
      bilateralTranslateL2 (2 * m + 2) g := countableUnitaryL2_forward_inverse σ _ _
  calc
    _ = ‖countableUnitaryL2 σ (bilateralRightWord_measurable G m)
        (countableUnitaryL2 σ (bilateralMiddleWord_measurable G m) (bilateralBlockA σ m g) -
          bilateralBlockB σ m g)‖ := (countableUnitaryL2_norm σ _ _).symm
    _ = ‖countableUnitaryL2 σ (bilateralIncrementProduct_measurable G (2 * m + 2)) g -
        bilateralTranslateL2 (2 * m + 2) g‖ := by
      rw [countableUnitaryL2_sub, bilateralBlock_collapse, hB]
    _ ≤ 2 * ‖f - g‖ := bilateral_l2_approximation_transport σ f g ht _

theorem bilateralBlock_centering (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (f g : Lp K 2 (bilateralWalkLaw G))
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω))
    (hg : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
      g (bilateralWalkLaw G)) :
    ‖bilateralBlockA σ m g - hilbertConstantL2 (bilateralWalkLaw G)
        (∫ ω, bilateralBlockA σ m g ω ∂bilateralWalkLaw G)‖ ≤ 2 * ‖f - g‖ ∧
    ‖bilateralBlockB σ m g - hilbertConstantL2 (bilateralWalkLaw G)
        (∫ ω, bilateralBlockB σ m g ω ∂bilateralWalkLaw G)‖ ≤ 2 * ‖f - g‖ := by
  borelize K
  have herror := bilateralBlock_error σ m f g ht
  constructor
  · exact (independent_unitary_variance_left σ (bilateralMiddleWord_measurable G m)
      (bilateralBlockA σ m g) (bilateralBlockB σ m g)
      (bilateralBlock_independent_left σ m g hg)).trans herror
  · exact (independent_unitary_variance_right σ (bilateralMiddleWord_measurable G m)
      (bilateralBlockA σ m g) (bilateralBlockB σ m g)
      (bilateralBlock_independent_right σ m g hg)).trans herror

end

end KadisonKastler

end OAI
