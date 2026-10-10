import OAI.Analysis.KadisonKastler.ModularSeparatedCuts
import OAI.Analysis.KadisonKastler.FrequencyActionAlignment

namespace OAI

/-! # From separated modular cuts to actual Fourier defects

The character moves the Fourier cut by one. Conjugating by the two
modular gauges then turns its off-diagonal block into multiplication by
the product of separated logarithmic spectral projections.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem field_norm_bound
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : RepresentsOperatorField volume F T) {e : ℝ} (he : 0 ≤ e)
    (hF : ∀ᵐ t, ‖F t‖ ≤ e) : ‖T‖ ≤ e := by
  apply ContinuousLinearMap.opNorm_le_bound _ he
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hT f, hF] with t ht hnorm
  rw [ht]
  exact ((F t).le_opNorm _).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

omit [CompleteSpace H] in
private theorem field_one_sub
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : RepresentsOperatorField volume F T) :
    RepresentsOperatorField volume (fun t => 1 - F t) (1 - T) := by
  intro f
  filter_upwards [hT f, Lp.coeFn_sub f (T f)] with t ht hs
  change (f - T f) t = (1 - F t) (f t)
  rw [hs]
  simp only [Pi.sub_apply, ht, sub_apply, one_apply_eq_self]

theorem norm_modular_gauge_cut_product_le
    {M N : VonNeumannAlgebra H} {Ω : H}
    (m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω)
    {e : ℝ} (he : 0 ≤ e)
    (hcuts : ∀ a, ‖(1 - n.upperCut (a - 1 / 2)) * m.upperCut (a + 1 / 2)‖ ≤ e)
    (a : ℝ) :
    ‖(1 - (star (regularGauge n.group n.continuous) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularFrequencyProjection (a - 1) *
        (regularGauge n.group n.continuous : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) *
      ((star (regularGauge m.group m.continuous) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularFrequencyProjection a *
        (regularGauge m.group m.continuous : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))‖ ≤ e := by
  rw [m.gauge_identity a, n.gauge_identity (a - 1)]
  let E := (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv
  let A := regularFieldOperator volume (fun ξ => n.upperCut (a - 1 - 2 * Real.pi * ξ))
    (n.measurable (a - 1)) 1 (Filter.Eventually.of_forall fun ξ => n.upper_contracts _)
  let B := regularFieldOperator volume (fun ξ => m.upperCut (a - 2 * Real.pi * ξ))
    (m.measurable a) 1 (Filter.Eventually.of_forall fun ξ => m.upper_contracts _)
  change ‖(1 - E A) * E B‖ ≤ e
  rw [← map_one E, ← map_sub E, ← map_mul E, StarAlgEquiv.norm_map]
  apply field_norm_bound
    ((field_one_sub (regularFieldOperator_represents volume _ _ _ _)).mul
      (regularFieldOperator_represents volume _ _ _ _)) he
  apply Filter.Eventually.of_forall
  intro ξ
  have h := hcuts (a - 1 / 2 - 2 * Real.pi * ξ)
  have hl : a - 1 / 2 - 2 * Real.pi * ξ - 1 / 2 = a - 1 - 2 * Real.pi * ξ := by ring
  have hh : a - 1 / 2 - 2 * Real.pi * ξ + 1 / 2 = a - 2 * Real.pi * ξ := by ring
  simpa only [hl, hh] using h

private theorem frequency_block_factorization
    (U V C : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (P Q : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hshift : (1 - P) * (C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * (1 - Q)) :
    (1 - P) * ((C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * (V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        (star U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) * P =
      (C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * V *
        ((1 - (star V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * Q * (V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) *
          ((star U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * P * (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))) *
        (star U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  have hV := Unitary.mul_star_self_of_mem V.property
  have hU := Unitary.mul_star_self_of_mem U.property
  simp only [mul_assoc] at hshift ⊢
  rw [← mul_assoc (1 - P) (C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H), hshift]
  simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc]
  simp only [hU, one_mul, mul_one,
    ← mul_assoc (V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (star V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H), hV]

theorem modular_comparison_multiplier
    {M N : VonNeumannAlgebra H} {Ω : H}
    (m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω)
    (hW : ∀ x, Continuous (fun t => (modularComparisonField m.group n.group t : H →L[ℂ] H) x)) :
    regularFieldOperator volume (modulatedUnitaryField (modularComparisonField m.group n.group))
      (fun x => (modulatedUnitaryField_continuous _ hW x).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall (norm_modulatedUnitaryField_le_one _)) =
    (regularCharacterUnitary (H := H) 1 : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
      (regularGauge n.group n.continuous : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
      (star (regularGauge m.group m.continuous) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularFieldOperator_represents volume _ _ _ _ f,
    regularCharacterUnitary_apply_ae 1
      ((regularGauge n.group n.continuous : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        ((star (regularGauge m.group m.continuous) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)),
    regularGauge_apply_ae n.group n.continuous
      ((star (regularGauge m.group m.continuous) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularGauge_star_apply_ae m.group m.continuous f] with t h₁ h₂ h₃ h₄
  change _ = (regularCharacterUnitary (H := H) 1 :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    ((regularGauge n.group n.continuous : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((star (regularGauge m.group m.continuous) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) t
  rw [h₁, h₂, h₃, h₄]
  simp only [modulatedUnitaryField, modularComparisonField, regularCharacterScalar,
    one_mul, smul_apply]
  rfl

theorem frequencyDefectBound_of_modular_cuts
    {M N : VonNeumannAlgebra H} {Ω : H}
    (m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω)
    (hW : ∀ x, Continuous (fun t => (modularComparisonField m.group n.group t : H →L[ℂ] H) x))
    {e : ℝ} (he : 0 ≤ e)
    (hcuts : ∀ a, ‖(1 - n.upperCut (a - 1 / 2)) * m.upperCut (a + 1 / 2)‖ ≤ e) :
    FrequencyDefectBound (modularComparisonField m.group n.group) hW e := by
  intro b
  rw [modular_comparison_multiplier m n hW]
  let a := -b
  let U := regularGauge m.group m.continuous
  let V := regularGauge n.group n.continuous
  let C := regularCharacterUnitary (H := H) 1
  change ‖(1 - regularFrequencyProjection a) *
    ((C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * (V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        (star U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) *
      regularFrequencyProjection a‖ ≤ e
  have hshift : (1 - regularFrequencyProjection a) *
      (C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        (1 - regularFrequencyProjection (a - 1)) := by
    have h := regularFrequencyProjection_character_intertwine (H := H) a (1 / (2 * Real.pi))
    have hc : 2 * Real.pi * (1 / (2 * Real.pi)) = 1 := by
      field_simp [Real.pi_ne_zero]
    rw [hc] at h
    dsimp [C]
    simpa only [sub_mul, mul_sub, one_mul, mul_one] using congrArg
      (fun T => (regularCharacterUnitary (H := H) 1 :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) - T) h
  rw [frequency_block_factorization U V C _ _ hshift]
  simp only [← Unitary.coe_star]
  rw [CStarRing.norm_mul_coe_unitary, mul_assoc,
    CStarRing.norm_coe_unitary_mul, CStarRing.norm_coe_unitary_mul]
  exact norm_modular_gauge_cut_product_le m n he hcuts a

end

end KadisonKastler

end OAI
