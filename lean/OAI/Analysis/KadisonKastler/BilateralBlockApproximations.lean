import OAI.Analysis.KadisonKastler.BilateralBlockEstimates
import OAI.Analysis.KadisonKastler.BilateralTranslateInverse

namespace OAI

/-! Positive- and negative-coordinate approximations to invariant coefficients. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {G K : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

def bilateralPositiveApprox (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G)) : Lp K 2 (bilateralWalkLaw G) :=
  countableUnitaryL2 (fun h => (σ h)⁻¹) (bilateralLeftWord_measurable G m)
    (hilbertConstantL2 (bilateralWalkLaw G) (∫ ω, bilateralBlockA σ m g ω ∂bilateralWalkLaw G))

def bilateralNegativeApprox (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G)) : Lp K 2 (bilateralWalkLaw G) :=
  bilateralTranslateL2 (-((2 * m + 2 : ℕ) : ℤ))
    (countableUnitaryL2 σ (bilateralRightWord_measurable G m)
      (hilbertConstantL2 (bilateralWalkLaw G) (∫ ω, bilateralBlockB σ m g ω ∂bilateralWalkLaw G)))

omit [InnerProductSpace ℂ K] [CompleteSpace K] [TopologicalSpace.SeparableSpace K] in
theorem hilbertConstantL2_coordinate (I : Set ℤ) (v : K) :
    AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) I]
      (hilbertConstantL2 (bilateralWalkLaw G) v) (bilateralWalkLaw G) :=
  aestronglyMeasurable_const.congr (hilbertConstantL2_ae v).symm

theorem bilateralPositiveApprox_coordinate (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G)) :
    AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | 0 ≤ j}]
      (bilateralPositiveApprox σ m g) (bilateralWalkLaw G) := by
  apply countableUnitaryL2_sigma
  · exact bilateralIncrementProduct_coordinate_measurable (m + 1)
      (by intro j _; change 0 ≤ (j : ℤ); omega)
  · exact hilbertConstantL2_coordinate _ _

theorem bilateralNegativeApprox_coordinate (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G)) :
    AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | j < 0}]
      (bilateralNegativeApprox σ m g) (bilateralWalkLaw G) := by
  have hR : Measurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | j < 2 * (m : ℤ) + 2}]
      (bilateralRightWord G m) :=
    bilateralIncrementProduct_shift_coordinate_measurable (m + 2) m
      (by intro j hj; change (j : ℤ) + (m + 2) < 2 * (m : ℤ) + 2; omega)
  have hc := countableUnitaryL2_sigma σ (bilateralRightWord_measurable G m) hR
    (hilbertConstantL2 (bilateralWalkLaw G) (∫ ω, bilateralBlockB σ m g ω ∂bilateralWalkLaw G))
    (hilbertConstantL2_coordinate _ _)
  have ht := bilateralTranslate_coordinate_aestronglyMeasurable (-((2 * m + 2 : ℕ) : ℤ))
    (show ∀ j ∈ {j : ℤ | j < 2 * (m : ℤ) + 2}, j + -((2 * m + 2 : ℕ) : ℤ) ∈ {j : ℤ | j < 0} from by
      intro j hj
      change j < 2 * (m : ℤ) + 2 at hj
      change j + -((2 * m + 2 : ℕ) : ℤ) < 0
      omega) hc
  exact ht.congr (bilateralTranslateL2_ae _ _).symm

theorem bilateralPositiveApprox_error (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (f g : Lp K 2 (bilateralWalkLaw G))
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω))
    (hg : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
      g (bilateralWalkLaw G)) :
    ‖f - bilateralPositiveApprox σ m g‖ ≤ 3 * ‖f - g‖ := by
  let a := hilbertConstantL2 (bilateralWalkLaw G) (∫ ω, bilateralBlockA σ m g ω ∂bilateralWalkLaw G)
  have hi : countableUnitaryL2 (fun h => (σ h)⁻¹) (bilateralLeftWord_measurable G m)
      (bilateralBlockA σ m g) = g := countableUnitaryL2_inv σ _ g
  have he : ‖g - bilateralPositiveApprox σ m g‖ = ‖bilateralBlockA σ m g - a‖ := by
    have hh := countableUnitaryL2_norm (fun h => (σ h)⁻¹) (bilateralLeftWord_measurable G m)
      (bilateralBlockA σ m g - a)
    rw [countableUnitaryL2_sub, hi] at hh
    exact hh
  calc
    _ ≤ ‖f - g‖ + ‖g - bilateralPositiveApprox σ m g‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖f - g‖ + ‖bilateralBlockA σ m g - a‖ := by rw [he]
    _ ≤ ‖f - g‖ + 2 * ‖f - g‖ := by have hc := (bilateralBlock_centering σ m f g ht hg).1; linarith
    _ = 3 * ‖f - g‖ := by ring

theorem bilateralNegativeApprox_error (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (f g : Lp K 2 (bilateralWalkLaw G))
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω))
    (hg : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
      g (bilateralWalkLaw G)) :
    ‖f - bilateralNegativeApprox σ m g‖ ≤ 3 * ‖f - g‖ := by
  let b := hilbertConstantL2 (bilateralWalkLaw G) (∫ ω, bilateralBlockB σ m g ω ∂bilateralWalkLaw G)
  let Rb := countableUnitaryL2 σ (bilateralRightWord_measurable G m) b
  have hi : countableUnitaryL2 σ (bilateralRightWord_measurable G m) (bilateralBlockB σ m g) =
      bilateralTranslateL2 (2 * m + 2) g := countableUnitaryL2_forward_inverse σ _ _
  have he : ‖bilateralTranslateL2 (2 * m + 2) g - Rb‖ = ‖bilateralBlockB σ m g - b‖ := by
    have hh := countableUnitaryL2_norm σ (bilateralRightWord_measurable G m) (bilateralBlockB σ m g - b)
    rw [countableUnitaryL2_sub, hi] at hh
    exact hh
  have hn : bilateralTranslateL2 (2 * m + 2) (bilateralNegativeApprox σ m g) = Rb :=
    bilateralTranslateL2_inverse _ _
  calc
    _ = ‖bilateralTranslateL2 (2 * m + 2) f - Rb‖ := by
      rw [← bilateralTranslateL2_norm (2 * m + 2) (f - bilateralNegativeApprox σ m g),
        bilateralTranslateL2_sub, hn]
    _ ≤ ‖bilateralTranslateL2 (2 * m + 2) f - bilateralTranslateL2 (2 * m + 2) g‖ +
        ‖bilateralTranslateL2 (2 * m + 2) g - Rb‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖f - g‖ + ‖bilateralBlockB σ m g - b‖ := by
      rw [← bilateralTranslateL2_sub, bilateralTranslateL2_norm, he]
    _ ≤ ‖f - g‖ + 2 * ‖f - g‖ := by have hc := (bilateralBlock_centering σ m f g ht hg).2; linarith
    _ = 3 * ‖f - g‖ := by ring

end

end KadisonKastler

end OAI
