import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles

namespace OAI

section

namespace Erdos3
open scoped BigOperators

variable {I : Type*} [Fintype I]

theorem affineProductProfile_weight_eq_shiftedSmooth
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i) (z : I → ℤ) :
    coefficientWeight (affineProductProfile c w) S z = profileWidthFactor w *
      rectangularWeight (smoothProductProfile I) (fun i => S i * c i)
        (fun i => S i * w i) z := by
  change coefficientWeight (affineProductProfile c w) S z = profileWidthFactor w *
    smoothProductProfile I (fun i => ((z i : ℝ) - S i * c i) / (S i * w i))
  simpa only [mul_comm] using affineProductProfile_sample c w S hw hS z

theorem affineProductProfile_mass_eq_shiftedSmooth
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i) :
    coefficientWeightSum (affineProductProfile c w) S = profileWidthFactor w *
      shiftedSmoothProductMass (fun i => S i * c i) (fun i => S i * w i) := by
  unfold coefficientWeightSum shiftedSmoothProductMass
  simp_rw [affineProductProfile_weight_eq_shiftedSmooth c w S hw hS]
  exact tsum_mul_left

theorem affineProductProfile_shiftedSmooth_mass_pos
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i)
    (hZ : 0 < coefficientWeightSum (affineProductProfile c w) S) :
    0 < shiftedSmoothProductMass (fun i => S i * c i) (fun i => S i * w i) := by
  rw [affineProductProfile_mass_eq_shiftedSmooth c w S hw hS] at hZ
  exact (mul_pos_iff_of_pos_left (profileWidthFactor_pos w hw)).mp hZ

theorem coefficientPMF_affineProductProfile_eq_shiftedSmooth
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → affineProductProfile c w x = 0)
    (hZ : 0 < coefficientWeightSum (affineProductProfile c w) S) :
    coefficientPMF (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
      S hS hsupport hZ =
      shiftedSmoothProductPMF (fun i => S i * c i) (fun i => S i * w i)
        (fun i => mul_pos (hS i) (hw i))
        (affineProductProfile_shiftedSmooth_mass_pos c w S hw hS hZ) := by
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [coefficientPMF_apply, shiftedSmoothProductPMF_toReal,
    affineProductProfile_weight_eq_shiftedSmooth c w S hw hS,
    affineProductProfile_mass_eq_shiftedSmooth c w S hw hS]
  exact mul_div_mul_left _ _ (profileWidthFactor_pos w hw).ne'

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)
    (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
    (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

include hR hσ hσ1 henormous in

theorem allocatedEnormous_shiftedSmooth_mass_pos :
    0 < shiftedSmoothProductMass
      (fun d => allocatedIntegerProfileScales B U basis S j i d *
        allocatedIntegerProfileCenters B R j i d)
      (fun d => allocatedIntegerProfileScales B U basis S j i d *
        allocatedIntegerProfileWidths B R σ j i d) :=
  affineProductProfile_shiftedSmooth_mass_pos _ _ _
    (allocatedIntegerProfileWidths_pos B hR hσ j i)
    (allocatedIntegerProfileScales_pos B U basis S j i)
    (allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous)

theorem allocatedEnormousProfilePMF_eq_shiftedSmooth :
    allocatedEnormousProfilePMF B U basis hR hσ S j i hσ1 henormous =
      shiftedSmoothProductPMF
        (fun d => allocatedIntegerProfileScales B U basis S j i d *
          allocatedIntegerProfileCenters B R j i d)
        (fun d => allocatedIntegerProfileScales B U basis S j i d *
          allocatedIntegerProfileWidths B R σ j i d)
        (fun d => mul_pos (allocatedIntegerProfileScales_pos B U basis S j i d)
          (allocatedIntegerProfileWidths_pos B hR hσ j i d))
        (allocatedEnormous_shiftedSmooth_mass_pos B U basis hR hσ S j i hσ1 henormous) :=
  coefficientPMF_affineProductProfile_eq_shiftedSmooth _ _ _
    (allocatedIntegerProfileWidths_pos B hR hσ j i)
    (allocatedIntegerProfileScales_pos B U basis S j i)
    (allocatedIntegerProfile_support B hR hσ j i hσ1)
    (allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous)

theorem allocatedEnormous_coefficient_law_shiftedSmooth :
    allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inr i⟩ =
      (shiftedSmoothProductPMF
        (fun d => allocatedIntegerProfileScales B U basis S j i d *
          allocatedIntegerProfileCenters B R j i d)
        (fun d => allocatedIntegerProfileScales B U basis S j i d *
          allocatedIntegerProfileWidths B R σ j i d)
        (fun d => mul_pos (allocatedIntegerProfileScales_pos B U basis S j i d)
          (allocatedIntegerProfileWidths_pos B hR hσ j i d))
        (allocatedEnormous_shiftedSmooth_mass_pos B U basis hR hσ S j i hσ1 henormous)).toMeasure := by
  rw [allocatedEnormous_coefficient_law B U basis hR hσ S j i hσ1 henormous,
    allocatedEnormousProfilePMF_eq_shiftedSmooth B U basis hR hσ S j i hσ1 henormous]

end VectorPolynomial
end Erdos3

end

end OAI
