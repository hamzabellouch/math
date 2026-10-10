import OAI.Analysis.KadisonKastler.CoreHalfFrequencyWindow
import OAI.Analysis.KadisonKastler.CoreFrequencyTranslation

namespace OAI

/-! # The regular core of a trivial action has a nontrivial center -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem regularIndicatorProjection_mul_eq_zero_of_disjoint
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    regularIndicatorProjection (H := H) s hs * regularIndicatorProjection t ht = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae s hs (regularIndicatorProjection t ht f),
    regularIndicatorProjection_apply_ae t ht f, Lp.coeFn_zero H 2 volume] with x h₁ h₂ h₀
  simp only [Pi.zero_apply] at h₀
  change regularIndicatorProjection s hs (regularIndicatorProjection t ht f) x =
    (0 : RegularCoreHilbert H) x
  rw [h₁, h₀]
  by_cases hx : x ∈ s
  · have hxt : x ∉ t := fun h => Set.disjoint_left.mp hst hx h
    rw [Set.indicator_of_mem hx, h₂, Set.indicator_of_notMem hxt]
  · exact Set.indicator_of_notMem hx _

theorem regularFrequencyWindow_mul_eq_zero_of_disjoint
    (a b c d : ℝ) (h : Disjoint (Set.Ioc a b) (Set.Ioc c d)) :
    regularFrequencyWindow (H := H) a b * regularFrequencyWindow c d = 0 := by
  unfold regularFrequencyWindow
  rw [← map_mul, regularIndicatorProjection_mul_eq_zero_of_disjoint _ _
    measurableSet_Ioc measurableSet_Ioc h, map_zero]

theorem regularFrequencyWindow_not_scalar [Nontrivial H] :
    ¬ ∃ z : ℂ, regularFrequencyWindow (H := H) 0 1 =
      z • (1 : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  rintro ⟨z, hz⟩
  let Q := regularCharacterUnitary (H := H) (2 * Real.pi * 1)
  have hfix : unitaryConj Q (regularFrequencyWindow 0 1) = regularFrequencyWindow 0 1 := by
    rw [hz]
    change (Q : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * (z • 1) *
      star (Q : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) = z • 1
    rw [mul_smul_comm, mul_one, smul_mul_assoc, Unitary.mul_star_self_of_mem Q.property]
  have he : regularFrequencyWindow (H := H) 1 2 = regularFrequencyWindow 0 1 := by
    simpa only [Q, zero_add, show (1 : ℝ) + 1 = 2 by norm_num] using
      (regularFrequencyWindow_character_conj (H := H) 0 1 1).symm.trans hfix
  have hzprod := regularFrequencyWindow_mul_eq_zero_of_disjoint (H := H) 0 1 1 2
    (Set.disjoint_left.mpr (by intro x hx hy; exact (not_lt_of_ge hx.2) hy.1))
  rw [he, (regularFrequencyWindow_isStarProjection (H := H) 0 1).isIdempotentElem.eq] at hzprod
  exact regularFrequencyWindow_unit_ne_zero hzprod

theorem regularFrequencyWindow_commute_of_translations
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ s, Commute T (regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) (a b : ℝ) :
    Commute T (regularFrequencyWindow a b) := by
  apply (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv.injective
  change (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv (T * regularFrequencyWindow a b) =
    (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv (regularFrequencyWindow a b * T)
  rw [map_mul, map_mul]
  have he : (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
      (regularFrequencyWindow (H := H) a b) =
      regularIndicatorProjection (Set.Ioc a b) measurableSet_Ioc := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [regularFrequencyWindow, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [he]
  exact (commute_scalarMultiplier_of_characters
    ((Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T)
    (fourier_commute_characters_of_translations T hT)
    ((Set.Ioc a b).indicator fun _ => (1 : ℂ))
    (measurable_const.indicator measurableSet_Ioc) 1
    (fun t => by by_cases ht : t ∈ Set.Ioc a b <;> simp [ht])).eq

theorem regularCore_not_factor_of_trivial [Nontrivial H]
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (htrivial : ∀ s, U s = 1) (M : VonNeumannAlgebra H) :
    ¬ ScalarCenter (regularCoreAlgebra U hU M) := by
  have hn : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M := by
    intro s a ha
    rw [htrivial s]
    change (1 : H →L[ℂ] H) * a * star (1 : H →L[ℂ] H) ∈ M
    simpa only [star_one, one_mul, mul_one] using ha
  intro hf
  apply regularFrequencyWindow_not_scalar (H := H)
  apply hf _ (regularFrequencyWindow_mem_core U hU M 0 1)
  intro T hT
  have hfixed := ((mem_fixedPointAlgebra_iff _ _ _).mp
    (regularCoreAlgebra_le_fixed U hU M hn hT)).2
  have htrans : ∀ s, Commute T (regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
    intro s
    have hs := hfixed s
    have hact : regularCoreAction U s = regularRightTranslation (H := H) s := by
      apply Subtype.ext
      change regularConstantHom volume (U s : H →L[ℂ] H) * _ = _
      rw [htrivial s]
      change regularConstantHom volume (1 : H →L[ℂ] H) * _ = _
      rw [map_one, one_mul]
    rw [hact] at hs
    exact ((commute_unitary_iff_star_right_conjugate
      (regularRightTranslation (H := H) s).property).mpr hs).symm
  exact (regularFrequencyWindow_commute_of_translations T htrans 0 1).eq

end

end KadisonKastler

end OAI
