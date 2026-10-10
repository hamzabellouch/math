import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Problem367

def gaussianSignalLikelihood (t : ℝ≥0) (s x : ℝ) : ℝ :=
  Real.exp (s * x - (t : ℝ) * s ^ 2 / 2)

theorem gaussianPDFReal_signal (t : ℝ≥0) (s x : ℝ) :
    gaussianPDFReal ((t : ℝ) * s) t x =
      gaussianPDFReal 0 t x * gaussianSignalLikelihood t s x := by
  by_cases ht : t = 0
  · simp [ht]
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have hexp : -(x - (t : ℝ) * s) ^ 2 / (2 * (t : ℝ)) =
      -(x - 0) ^ 2 / (2 * (t : ℝ)) + (s * x - (t : ℝ) * s ^ 2 / 2) := by
    field_simp
    ring
  simp only [gaussianPDFReal, gaussianSignalLikelihood, hexp, Real.exp_add]
  ring

theorem gaussianPDF_signal (t : ℝ≥0) (s x : ℝ) :
    gaussianPDF ((t : ℝ) * s) t x =
      gaussianPDF 0 t x * ENNReal.ofReal (gaussianSignalLikelihood t s x) := by
  rw [gaussianPDF, gaussianPDFReal_signal, ENNReal.ofReal_mul
    (gaussianPDFReal_nonneg 0 t x)]
  rfl

theorem gaussianReal_signal_withDensity (t : ℝ≥0) (s : ℝ) :
    gaussianReal ((t : ℝ) * s) t =
      (gaussianReal 0 t).withDensity
        (fun x => ENNReal.ofReal (gaussianSignalLikelihood t s x)) := by
  by_cases ht : t = 0
  · simp [ht, gaussianSignalLikelihood, MeasureTheory.dirac_withDensity]
  rw [gaussianReal_of_var_ne_zero _ ht, gaussianReal_of_var_ne_zero _ ht,
    ← withDensity_mul volume (measurable_gaussianPDF 0 t) (by
      unfold gaussianSignalLikelihood
      fun_prop)]
  congr 1
  funext x
  exact gaussianPDF_signal t s x

theorem lintegral_pi_prod_of_measurable
    {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)]
    (mu : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)]
    (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi mu) = ∏ i, ∫⁻ x, f i x ∂mu i := by
  classical
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun (i : I) (x : ∀ j, X j) => f i (x i))
      (iIndepFun_pi (μ := mu) (X := f) (fun i => (hf i).aemeasurable))
    (fun i => (hf i).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i hi
  exact (measurePreserving_eval mu i).lintegral_comp (hf i)

theorem pi_withDensity_of_probability
    {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)]
    (mu nu : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (mu i)] [∀ i, SigmaFinite (nu i)]
    (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (hnu : ∀ i, nu i = (mu i).withDensity (f i)) :
    Measure.pi nu = (Measure.pi mu).withDensity (fun x => ∏ i, f i (x i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  have hpi : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.pi Set.countable_univ
    (fun i hi => hs i)
  rw [withDensity_apply _ hpi, ← lintegral_indicator hpi]
  have hind : (Set.pi Set.univ s).indicator (fun x => ∏ i, f i (x i)) =
      fun x => ∏ i, (s i).indicator (f i) (x i) := by
    funext x
    by_cases hx : ∀ i, x i ∈ s i
    · have hmem : x ∈ Set.pi Set.univ s := by simpa using hx
      rw [Set.indicator_of_mem hmem]
      exact Finset.prod_congr rfl (fun i hi => (Set.indicator_of_mem (hx i) _).symm)
    · obtain ⟨i, hi⟩ := not_forall.mp hx
      have hmem : x ∉ Set.pi Set.univ s := by simpa using not_forall.mpr ⟨i, hi⟩
      rw [Set.indicator_of_notMem hmem]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind, lintegral_pi_prod_of_measurable mu _ (fun i => (hf i).indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hnu i, withDensity_apply _ (hs i), lintegral_indicator (hs i)]

def gaussianVectorLikelihood {I : Type*} [Fintype I]
    (t : ℝ≥0) (s x : I → ℝ) : ℝ :=
  Real.exp ((∑ i, s i * x i) - (t : ℝ) / 2 * ∑ i, s i ^ 2)

theorem prod_gaussianSignalLikelihood {I : Type*} [Fintype I]
    (t : ℝ≥0) (s x : I → ℝ) :
    (∏ i, gaussianSignalLikelihood t (s i) (x i)) = gaussianVectorLikelihood t s x := by
  classical
  simp only [gaussianSignalLikelihood, gaussianVectorLikelihood, ← Real.exp_sum]
  congr 1
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_div, ← Finset.mul_sum]
  ring

theorem gaussianPi_signal_withDensity {I : Type*} [Fintype I]
    (t : ℝ≥0) (s : I → ℝ) :
    Measure.pi (fun i => gaussianReal ((t : ℝ) * s i) t) =
      (Measure.pi (fun _ : I => gaussianReal 0 t)).withDensity
        (fun x => ENNReal.ofReal (gaussianVectorLikelihood t s x)) := by
  classical
  calc
    Measure.pi (fun i => gaussianReal ((t : ℝ) * s i) t) =
        (Measure.pi (fun _ : I => gaussianReal 0 t)).withDensity
          (fun x => ∏ i, ENNReal.ofReal (gaussianSignalLikelihood t (s i) (x i))) := by
      exact pi_withDensity_of_probability
        (fun _ : I => gaussianReal 0 t)
        (fun i : I => gaussianReal ((t : ℝ) * s i) t)
        (fun i : I => fun x : ℝ => ENNReal.ofReal (gaussianSignalLikelihood t (s i) x))
        (fun i => by unfold gaussianSignalLikelihood; fun_prop)
        (fun i => gaussianReal_signal_withDensity t (s i))
    _ = _ := by
      apply withDensity_congr_ae
      filter_upwards [] with x
      calc
        (∏ i, ENNReal.ofReal (gaussianSignalLikelihood t (s i) (x i))) =
            ENNReal.ofReal (∏ i, gaussianSignalLikelihood t (s i) (x i)) :=
          (ENNReal.ofReal_prod_of_nonneg (fun i hi => by
            unfold gaussianSignalLikelihood
            positivity)).symm
        _ = ENNReal.ofReal (gaussianVectorLikelihood t s x) :=
          congrArg ENNReal.ofReal (prod_gaussianSignalLikelihood t s x)

theorem gaussianVectorLikelihood_of_sq_eq_one {I : Type*} [Fintype I]
    (t : ℝ≥0) (s x : I → ℝ) (hs : ∀ i, s i ^ 2 = 1) :
    gaussianVectorLikelihood t s x =
      Real.exp ((∑ i, s i * x i) - (t : ℝ) * Fintype.card I / 2) := by
  classical
  unfold gaussianVectorLikelihood
  simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  congr 1
  ring

theorem gaussianPi_spin_withDensity {I : Type*} [Fintype I]
    (t : ℝ≥0) (s : I → ℝ) (hs : ∀ i, s i ^ 2 = 1) :
    Measure.pi (fun i => gaussianReal ((t : ℝ) * s i) t) =
      (Measure.pi (fun _ : I => gaussianReal 0 t)).withDensity
        (fun x => ENNReal.ofReal
          (Real.exp ((∑ i, s i * x i) - (t : ℝ) * Fintype.card I / 2))) := by
  simpa only [gaussianVectorLikelihood_of_sq_eq_one t s _ hs] using
    gaussianPi_signal_withDensity t s

end Problem367

end

end OAI
