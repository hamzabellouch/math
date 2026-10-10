import Mathlib.MeasureTheory.Function.JacobianOneDim
import OAI.NumberTheory.Jacobsthal.Estimates.HarmonicChangeOfVariable
import OAI.NumberTheory.Jacobsthal.Paths.AdmittedHarmonicPaths
import OAI.NumberTheory.Jacobsthal.Probability.HarmonicPrefixKernel

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.HarmonicExponentMeasure

open Set MeasureTheory
open scoped ENNReal
open FinitePathGeometry HarmonicChangeOfVariable

theorem nextExponent_measurable (r : ℝ) : Measurable (nextExponent r) :=
  measurable_const.div (measurable_id.add_const 1)

theorem exponent_image_Ici {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    nextExponent r '' Ici a = Ioc 0 (nextExponent r a) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    change a ≤ t at ht
    refine ⟨nextExponent_pos hr (ha.trans_le ht), ?_⟩
    exact div_le_div_of_nonneg_left hr.le (by linarith : 0 < a + 1) (by linarith)
  · intro hx
    refine ⟨r / x - 1, ?_, ?_⟩
    · change a ≤ r / x - 1
      have hm := (le_div_iff₀ (by linarith : 0 < a + 1)).mp hx.2
      have hd : a + 1 ≤ r / x := (le_div_iff₀ hx.1).mpr (by nlinarith)
      linarith
    · unfold nextExponent
      simp only [sub_add_cancel]
      field_simp [hr.ne', hx.1.ne']

theorem nextExponent_injOn {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    InjOn (nextExponent r) (Ici a) := by
  intro t ht u hu heq
  have h := congrArg (fun x : ℝ => r / x - 1) heq
  simpa only [inverse_exponent hr (ha.trans_le ht), inverse_exponent hr (ha.trans_le hu)] using h

theorem harmonic_lintegral_substitution {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (H : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ici a, ENNReal.ofReal (1 / (t + 1)) * H (nextExponent r t)) =
      ∫⁻ x in Ioc 0 (nextExponent r a), ENNReal.ofReal x⁻¹ * H x := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := nextExponent r)
    (f' := fun t => -r / (t + 1)^2) measurableSet_Ici
    (fun t ht => (exponent_hasDerivAt (r := r) (ha.trans_le ht)).hasDerivWithinAt)
    (nextExponent_injOn hr ha) (fun x => ENNReal.ofReal x⁻¹ * H x)
  rw [exponent_image_Ici hr ha] at h
  rw [h]
  apply lintegral_congr_ae
  apply ae_restrict_of_forall_mem measurableSet_Ici
  intro t ht
  have ht0 := ha.trans_le ht
  have hx := nextExponent_pos hr ht0
  have heq : |(-r / (t + 1)^2)| * (nextExponent r t)⁻¹ = 1 / (t + 1) := by
    have hj := harmonic_jacobian hr ht0
    rw [(exponent_hasDerivAt (r := r) ht0).deriv] at hj
    simpa only [div_eq_mul_inv] using hj
  dsimp only
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), heq]

noncomputable def ratioMeasure (a : ℝ) : Measure ℝ :=
  (volume.restrict (Ici a)).withDensity (fun t : ℝ => ENNReal.ofReal (1 / (t + 1)))

noncomputable def exponentMeasure (b : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc 0 b)).withDensity (fun x : ℝ => ENNReal.ofReal x⁻¹)

theorem ratioMeasure_map {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    (ratioMeasure a).map (nextExponent r) = exponentMeasure (nextExponent r a) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH (nextExponent_measurable r)]
  unfold ratioMeasure exponentMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ (f := fun t : ℝ => ENNReal.ofReal (1 / (t + 1)))
      (g := fun t : ℝ => H (nextExponent r t)) (by fun_prop)
      (hH.comp (nextExponent_measurable r)),
    lintegral_withDensity_eq_lintegral_mul _ (f := fun x : ℝ => ENNReal.ofReal x⁻¹) (g := H) (by fun_prop) hH]
  exact harmonic_lintegral_substitution hr ha H

noncomputable def inverseRatio (r x : ℝ) : ℝ := r / x - 1

theorem inverseRatio_measurable (r : ℝ) : Measurable (inverseRatio r) :=
  (measurable_const.div measurable_id).sub_const 1

theorem inverse_lintegral_substitution {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (H : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ici a, ENNReal.ofReal (1 / (t + 1)) * H t) =
      ∫⁻ x in Ioc 0 (nextExponent r a), ENNReal.ofReal x⁻¹ * H (inverseRatio r x) := by
  calc
    _ = ∫⁻ t in Ici a, ENNReal.ofReal (1 / (t + 1)) * H (inverseRatio r (nextExponent r t)) := by
      apply lintegral_congr_ae
      apply ae_restrict_of_forall_mem measurableSet_Ici
      intro t ht
      dsimp only
      rw [inverseRatio, inverse_exponent hr (ha.trans_le ht)]
    _ = _ := harmonic_lintegral_substitution hr ha (fun x => H (inverseRatio r x))

theorem exponentMeasure_map {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    (exponentMeasure (nextExponent r a)).map (inverseRatio r) = ratioMeasure a := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH (inverseRatio_measurable r)]
  unfold ratioMeasure exponentMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ (f := fun x : ℝ => ENNReal.ofReal x⁻¹)
      (g := fun x : ℝ => H (inverseRatio r x)) (by fun_prop) (hH.comp (inverseRatio_measurable r)),
    lintegral_withDensity_eq_lintegral_mul _ (f := fun t : ℝ => ENNReal.ofReal (1 / (t + 1)))
      (g := H) (by fun_prop) hH]
  exact (inverse_lintegral_substitution hr ha H).symm

theorem ratioMeasure_map_update {β : Type*} [MeasurableSpace β]
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (U : ℝ → β) (hU : Measurable U) :
    (ratioMeasure a).map U =
      (exponentMeasure (nextExponent r a)).map (fun x => U (inverseRatio r x)) := by
  rw [← exponentMeasure_map hr ha, Measure.map_map hU (inverseRatio_measurable r)]
  rfl

theorem accepted_exponent_measure {r a ell : ℝ} (hr : 0 < r) (ha : 0 < a) (hell : 0 ≤ ell) :
    ((ratioMeasure a).restrict {t | ell < nextExponent r t}).map (nextExponent r) =
      (volume.restrict (Ioc ell (nextExponent r a))).withDensity (fun x : ℝ => ENNReal.ofReal x⁻¹) := by
  change ((ratioMeasure a).restrict ((nextExponent r) ⁻¹' Ioi ell)).map (nextExponent r) = _
  rw [← Measure.restrict_map (nextExponent_measurable r) (s := Ioi ell) measurableSet_Ioi, ratioMeasure_map hr ha]
  unfold exponentMeasure
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  congr 2
  ext x
  simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
  constructor
  · rintro ⟨hx, _, hu⟩
    exact ⟨hx, hu⟩
  · intro hx
    exact ⟨hx.1, lt_of_le_of_lt hell hx.1, hx.2⟩

end NumberTheoryLean.HarmonicExponentMeasure

end

section

namespace NumberTheoryLean.HarmonicExponentRows

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open HarmonicExponentMeasure HarmonicKernelDensities HarmonicWeightKernel
open ArrivalKernelGeometry AdmittedHarmonicPaths RegeneratingInverseBands
open Erdos970Dependency.OrdinaryKernelInvariance

 theorem exponentMeasure_restrict (b : ℝ) {ell : ℝ} (hell : 0 ≤ ell) :
    (exponentMeasure b).restrict (Ioi ell) =
      (volume.restrict (Ioc ell b)).withDensity (fun x : ℝ => ENNReal.ofReal x⁻¹) := by
  unfold exponentMeasure
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  congr 2
  ext x
  simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
  constructor
  · rintro ⟨hx, _, hu⟩; exact ⟨hx, hu⟩
  · intro hx; exact ⟨hx.1, lt_of_le_of_lt hell hx.1, hx.2⟩

theorem exponentMeasure_ae_interval (b : ℝ) :
    ∀ᵐ x ∂exponentMeasure b, x ∈ Ioc 0 b := by
  unfold exponentMeasure
  rw [ae_withDensity_iff (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal x⁻¹))]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
  intro _
  exact hx

theorem accepted_update_measure {β : Type*} [MeasurableSpace β]
    {r a ell : ℝ} (hr : 0 < r) (ha : 0 < a) (hell : 0 ≤ ell)
    (U : ℝ → β) (hU : Measurable U) (A : Set β) (hA : MeasurableSet A)
    (hcut : ∀ t, a ≤ t → (U t ∈ A ↔ ell < nextExponent r t)) :
    ((ratioMeasure a).map U).restrict A =
      ((volume.restrict (Ioc ell (nextExponent r a))).withDensity
        (fun x : ℝ => ENNReal.ofReal x⁻¹)).map (fun x => U (inverseRatio r x)) := by
  rw [ratioMeasure_map_update hr ha U hU,
    Measure.restrict_map (f := fun x => U (inverseRatio r x)) (hU.comp (inverseRatio_measurable r)) hA]
  have hEq : (fun x => U (inverseRatio r x)) ⁻¹' A =ᵐ[exponentMeasure (nextExponent r a)] Ioi ell := by
    filter_upwards [exponentMeasure_ae_interval (nextExponent r a)] with x hx
    obtain ⟨t, ht, rfl⟩ := (exponent_image_Ici hr ha).symm.subset hx
    apply propext
    change U (inverseRatio r (nextExponent r t)) ∈ A ↔ ell < nextExponent r t
    rw [inverseRatio, HarmonicChangeOfVariable.inverse_exponent hr (ha.trans_le ht)]
    exact hcut t ht
  rw [Measure.restrict_congr_set hEq, exponentMeasure_restrict _ hell]

theorem harmonic_even_ratioMeasure (s : EvenState) (T : ℝ) :
    harmonicKernel (.inl s, T) = (ratioMeasure (s.1 - 1)).map (evenUpdateReal T) := by
  rw [harmonic_even_measure]
  unfold harmonicRatioDensity
  rw [withDensity_indicator measurableSet_Ici]
  rfl

theorem harmonic_odd_ratioMeasure (s : OddState) (T : ℝ) :
    harmonicKernel (.inr s, T) = (ratioMeasure (max 2 (s.1 - 1))).map (oddUpdateReal T) := by
  rw [harmonic_odd_measure]
  unfold harmonicRatioDensity
  rw [withDensity_indicator measurableSet_Ici]
  rfl

theorem evenUpdate_exponent (v T : ℝ) (s : EvenState) {t : ℝ} (ht : s.1 - 1 ≤ t) :
    currentExponent v (evenUpdateReal T t) = nextExponent (Real.exp (v - T)) t := by
  have hratio : stateRatio (.inr (oddLift t)) = t := by
    change max (95 / 100 : ℝ) t = t
    apply max_eq_right
    linarith [s.2]
  change currentExponent v (.inr (oddLift t), T + cost t) = _
  simpa only [hratio, gapValue] using currentExponent_update v ((.inl s), T) (.inr (oddLift t))

theorem oddUpdate_exponent (v T : ℝ) (s : OddState) {t : ℝ} (ht : max 2 (s.1 - 1) ≤ t) :
    currentExponent v (oddUpdateReal T t) = nextExponent (Real.exp (v - T)) t := by
  have hratio : stateRatio (.inl (evenLift t)) = t := by
    change max (198 / 100 : ℝ) t = t
    apply max_eq_right
    linarith [le_max_left (2 : ℝ) (s.1 - 1)]
  change currentExponent v (.inl (evenLift t), T + cost t) = _
  simpa only [hratio, gapValue] using currentExponent_update v ((.inr s), T) (.inl (evenLift t))

theorem admitted_even_exponent_row (v T : ℝ) (s : EvenState) {ell : ℝ} (hell : 0 ≤ ell) :
    admittedHarmonic v ell (.inl s, T) =
      ((volume.restrict (Ioc ell (Real.exp (v - T) / s.1))).withDensity
        (fun x : ℝ => ENNReal.ofReal x⁻¹)).map
          (fun x => evenUpdateReal T (inverseRatio (Real.exp (v - T)) x)) := by
  rw [admittedHarmonic, Kernel.restrict_apply, harmonic_even_ratioMeasure]
  have h := accepted_update_measure (Real.exp_pos (v - T))
    (by linarith [s.2] : 0 < s.1 - 1) hell (evenUpdateReal T) (evenUpdateReal_measurable T)
    (arrivalSet v ell) (arrivalSet_measurable v ell) (fun t ht => by
      change ell < currentExponent v (evenUpdateReal T t) ↔ _
      rw [evenUpdate_exponent v T s ht])
  simpa only [nextExponent, sub_add_cancel] using h

theorem admitted_odd_exponent_row (v T : ℝ) (s : OddState) {ell : ℝ} (hell : 0 ≤ ell) :
    admittedHarmonic v ell (.inr s, T) =
      ((volume.restrict (Ioc ell (nextExponent (Real.exp (v - T)) (max 2 (s.1 - 1))))).withDensity
        (fun x : ℝ => ENNReal.ofReal x⁻¹)).map
          (fun x => oddUpdateReal T (inverseRatio (Real.exp (v - T)) x)) := by
  rw [admittedHarmonic, Kernel.restrict_apply, harmonic_odd_ratioMeasure]
  exact accepted_update_measure (Real.exp_pos (v - T))
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)) hell
    (oddUpdateReal T) (oddUpdateReal_measurable T) (arrivalSet v ell) (arrivalSet_measurable v ell)
    (fun t ht => by
      change ell < currentExponent v (oddUpdateReal T t) ↔ _
      rw [oddUpdate_exponent v T s ht])

end NumberTheoryLean.HarmonicExponentRows

end

section

namespace NumberTheoryLean.AdmittedExponentMarginal

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open HarmonicExponentMeasure HarmonicExponentRows HarmonicKernelDensities
open ArrivalKernelGeometry AdmittedHarmonicPaths

 theorem inverse_update_marginal {β : Type*} [MeasurableSpace β]
    {r a ell : ℝ} (hr : 0 < r) (ha : 0 < a) (hell : 0 ≤ ell)
    (U : ℝ → β) (hU : Measurable U) (V : β → ℝ) (hV : Measurable V)
    (hVU : ∀ t, a ≤ t → V (U t) = nextExponent r t) :
    ((((volume.restrict (Ioc ell (nextExponent r a))).withDensity
      (fun x : ℝ => ENNReal.ofReal x⁻¹)).map (fun x => U (inverseRatio r x))).map V) =
      (volume.restrict (Ioc ell (nextExponent r a))).withDensity (fun x : ℝ => ENNReal.ofReal x⁻¹) := by
  let μ := (volume.restrict (Ioc ell (nextExponent r a))).withDensity (fun x : ℝ => ENNReal.ofReal x⁻¹)
  have hs : ∀ᵐ x ∂μ, x ∈ Ioc ell (nextExponent r a) :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioc)
  have hEq : (V ∘ (fun x => U (inverseRatio r x))) =ᵐ[μ] id := by
    filter_upwards [hs] with x hx
    have hx' : x ∈ Ioc 0 (nextExponent r a) := ⟨lt_of_le_of_lt hell hx.1, hx.2⟩
    obtain ⟨t, ht, rfl⟩ := (exponent_image_Ici hr ha).symm.subset hx'
    change V (U (inverseRatio r (nextExponent r t))) = nextExponent r t
    rw [inverseRatio, HarmonicChangeOfVariable.inverse_exponent hr (ha.trans_le ht)]
    exact hVU t ht
  rw [Measure.map_map (f := fun x => U (inverseRatio r x)) hV (hU.comp (inverseRatio_measurable r))]
  exact (Measure.map_congr hEq).trans Measure.map_id

theorem admitted_even_exponent_marginal (v T : ℝ) (s : EvenState) {ell : ℝ} (hell : 0 ≤ ell) :
    (admittedHarmonic v ell (.inl s, T)).map (currentExponent v) =
      ErdosPrimeInputs.HarmonicPrefixKernel.kernel ell (currentExponent v (.inl s, T)) := by
  rw [admitted_even_exponent_row v T s hell, ErdosPrimeInputs.HarmonicPrefixKernel.kernel_eq_restrict]
  have h := inverse_update_marginal (Real.exp_pos (v - T))
    (by linarith [s.2] : 0 < s.1 - 1) hell (evenUpdateReal T) (evenUpdateReal_measurable T)
    (currentExponent v) (currentExponent_measurable v) (fun t ht => evenUpdate_exponent v T s ht)
  simpa only [nextExponent, sub_add_cancel, currentExponent, RegeneratingInverseBands.gapValue,
    stateRatio, Sum.elim_inl] using h

theorem admitted_odd_exponent_marginal (v T : ℝ) (s : OddState) {ell : ℝ} (hell : 0 ≤ ell) :
    (admittedHarmonic v ell (.inr s, T)).map (currentExponent v) =
      ErdosPrimeInputs.HarmonicPrefixKernel.kernel ell
        (nextExponent (Real.exp (v - T)) (max 2 (s.1 - 1))) := by
  rw [admitted_odd_exponent_row v T s hell, ErdosPrimeInputs.HarmonicPrefixKernel.kernel_eq_restrict]
  exact inverse_update_marginal (Real.exp_pos (v - T))
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)) hell
    (oddUpdateReal T) (oddUpdateReal_measurable T) (currentExponent v) (currentExponent_measurable v)
    (fun t ht => oddUpdate_exponent v T s ht)

theorem harmonic_cutoff_mono (ell : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ErdosPrimeInputs.HarmonicPrefixKernel.kernel ell a ≤
      ErdosPrimeInputs.HarmonicPrefixKernel.kernel ell b := by
  rw [ErdosPrimeInputs.HarmonicPrefixKernel.kernel_eq_restrict,
    ErdosPrimeInputs.HarmonicPrefixKernel.kernel_eq_restrict,
    ← withDensity_indicator measurableSet_Ioc, ← withDensity_indicator measurableSet_Ioc]
  apply withDensity_mono
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ Ioc ell a
  · have hx' : x ∈ Ioc ell b := ⟨hx.1, hx.2.trans hab⟩
    rw [indicator_of_mem hx, indicator_of_mem hx']
  · rw [indicator_of_notMem hx]
    exact zero_le

theorem admitted_exponent_marginal_le (v : ℝ) {ell : ℝ} (hell : 0 ≤ ell) (z : CostState) :
    (admittedHarmonic v ell z).map (currentExponent v) ≤
      ErdosPrimeInputs.HarmonicPrefixKernel.kernel ell (currentExponent v z) := by
  rcases z with ⟨s, T⟩
  cases s with
  | inl s => exact (admitted_even_exponent_marginal v T s hell).le
  | inr s =>
    rw [admitted_odd_exponent_marginal v T s hell]
    apply harmonic_cutoff_mono
    exact exponent_le_cutoff (i := .odd) (s := s.1) s.2 le_rfl (Real.exp_pos (v - T))

end NumberTheoryLean.AdmittedExponentMarginal

end

end Erdos970

end OAI
