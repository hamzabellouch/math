import OAI.Analysis.PureInfiniteness.SpectralProductCFC
import OAI.Analysis.PureInfiniteness.JointSpectralEstimates

namespace OAI

/-! Evaluation of the finite spectral partition at characters. These formulas
reduce the joint estimates to their scalar versions without spectral measures. -/

noncomputable section
open scoped BigOperators ComplexOrder
open WeakDual

namespace WeakPureInfiniteness

variable {D : Type*} [CommCStarAlgebra D]

def spectralCharacter (χ : characterSpace ℂ D) : D →⋆ₐ[ℂ] ℂ :=
  (ContinuousMap.evalStarAlgHom ℂ ℂ χ).comp (gelfandStarTransform D).toStarAlgHom

lemma scalarStarHom_eq_real (φ : D →⋆ₐ[ℂ] ℂ) {a : D}
    (ha : IsSelfAdjoint a) : φ a = ((φ a).re : ℂ) := by
  have h := congrArg Complex.im (ha.map (φ)).star_eq
  have hz : (φ a).im = 0 := by
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  exact Complex.ext rfl (by simpa using hz)

lemma scalarStarHom_cfc (φ : D →⋆ₐ[ℂ] ℂ) (f : ℝ → ℝ)
    (a : D) (ha : IsSelfAdjoint a) (hf : Continuous f) :
    φ (cfc f a) = (f (φ a).re : ℂ) := by
  rw [(φ).map_cfc f a hf.continuousOn
    (by fun_prop) ha (ha.map (φ))]
  conv_lhs => arg 2; rw [scalarStarHom_eq_real φ ha]
  exact cfc_algebraMap (R := ℝ) (A := ℂ) _ f

lemma norm_le_of_spectralCharacters (a : D) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ χ, ‖spectralCharacter χ a‖ ≤ C) : ‖a‖ ≤ C := by
  rw [← StarAlgEquiv.norm_map (gelfandStarTransform D) a]
  exact (ContinuousMap.norm_le _ hC).mpr h

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma scalarStarHom_productGridHat (φ : D →⋆ₐ[ℂ] ℂ) (a : I → D)
    (ha : ∀ i, IsSelfAdjoint (a i)) (r : ℝ) (s : I → Finset ℤ) (k : SpectralGridCell s) :
    φ (productGridHatElement a r s k) =
      (productGridHat s k (fun i => (φ (a i)).re / r) : ℂ) := by
  unfold productGridHatElement productGridHat gridHatElement
  rw [map_prod, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact scalarStarHom_cfc φ _ _ (ha i)
    ((continuous_gridHat (k i)).comp (continuous_id.div_const r))

omit [DecidableEq I] in
lemma scalarStarHom_productGridPlateau (φ : D →⋆ₐ[ℂ] ℂ) (a : I → D)
    (ha : ∀ i, IsSelfAdjoint (a i)) (r : ℝ) (s : I → Finset ℤ) (k : SpectralGridCell s) :
    φ (productGridPlateauElement a r s k) =
      (productGridPlateau s k (fun i => (φ (a i)).re / r) : ℂ) := by
  unfold productGridPlateauElement productGridPlateau gridPlateauElement
  rw [map_prod, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact scalarStarHom_cfc φ _ _ (ha i)
    ((continuous_gridPlateau (k i)).comp (continuous_id.div_const r))

omit [DecidableEq I] in
lemma norm_productGridHatElement_le_one (a : I → D) (ha : ∀ i, IsSelfAdjoint (a i))
    (r : ℝ) (s : I → Finset ℤ) (k : SpectralGridCell s) :
    ‖productGridHatElement a r s k‖ ≤ 1 := by
  apply norm_le_of_spectralCharacters _ _ zero_le_one
  intro χ
  rw [scalarStarHom_productGridHat _ a ha, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (productGridHat_nonneg _ _ _)]
  exact productGridHat_le_one _ _ _

omit [DecidableEq I] in
lemma norm_productGridPlateauElement_le_one (a : I → D) (ha : ∀ i, IsSelfAdjoint (a i))
    (r : ℝ) (s : I → Finset ℤ) (k : SpectralGridCell s) :
    ‖productGridPlateauElement a r s k‖ ≤ 1 := by
  apply norm_le_of_spectralCharacters _ _ zero_le_one
  intro χ
  rw [scalarStarHom_productGridPlateau _ a ha, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (productGridPlateau_bounds _ _ _).1]
  exact (productGridPlateau_bounds _ _ _).2

end WeakPureInfiniteness

end

end OAI
