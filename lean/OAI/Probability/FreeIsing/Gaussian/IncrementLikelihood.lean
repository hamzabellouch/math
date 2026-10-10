import OAI.Probability.FreeIsing.Gaussian.Likelihood

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Problem367

theorem map_withDensity_comp_observation
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) (F : X → Y) (hF : Measurable F)
    (L : Y → ℝ≥0∞) (hL : Measurable L) :
    Measure.map F (mu.withDensity (L ∘ F)) =
      (Measure.map F mu).withDensity L := by
  ext s hs
  rw [Measure.map_apply hF hs, withDensity_apply _ (hs.preimage hF),
    withDensity_apply _ hs, Measure.restrict_map hF hs, lintegral_map hL hF]
  rfl

theorem gaussianPi_variable_signal_withDensity {I : Type*} [Fintype I]
    (t : I → ℝ≥0) (s : I → ℝ) :
    Measure.pi (fun i => gaussianReal ((t i : ℝ) * s i) (t i)) =
      (Measure.pi (fun i => gaussianReal 0 (t i))).withDensity
        (fun x : I → ℝ => ENNReal.ofReal
          (Real.exp (∑ i : I, (s i * x i - (t i : ℝ) * s i ^ 2 / 2)))) := by
  classical
  calc
    Measure.pi (fun i => gaussianReal ((t i : ℝ) * s i) (t i)) =
        (Measure.pi (fun i => gaussianReal 0 (t i))).withDensity
          (fun x => ∏ i, ENNReal.ofReal (gaussianSignalLikelihood (t i) (s i) (x i))) := by
      exact pi_withDensity_of_probability
        (fun i => gaussianReal 0 (t i))
        (fun i => gaussianReal ((t i : ℝ) * s i) (t i))
        (fun i x => ENNReal.ofReal (gaussianSignalLikelihood (t i) (s i) x))
        (fun i => by unfold gaussianSignalLikelihood; fun_prop)
        (fun i => gaussianReal_signal_withDensity (t i) (s i))
    _ = _ := by
      apply withDensity_congr_ae
      filter_upwards [] with x
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i hi => by
        unfold gaussianSignalLikelihood; positivity)]
      simp only [gaussianSignalLikelihood, ← Real.exp_sum]

theorem gaussianIncrements_signal_withDensity {I : Type*} [Fintype I]
    (t : I → ℝ≥0) (s : ℝ) :
    Measure.pi (fun i => gaussianReal ((t i : ℝ) * s) (t i)) =
      (Measure.pi (fun i => gaussianReal 0 (t i))).withDensity
        (fun x => ENNReal.ofReal
          (gaussianSignalLikelihood (∑ i, t i) s (∑ i, x i))) := by
  classical
  rw [gaussianPi_variable_signal_withDensity]
  congr 1
  funext x
  congr 1
  unfold gaussianSignalLikelihood
  congr 1
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div,
    ← Finset.sum_mul, NNReal.coe_sum]

def cumulativeObservation {n : ℕ} (x : Fin n → ℝ) (k : Fin (n + 1)) : ℝ :=
  ∑ i : Fin n, if i.val < k.val then x i else 0

theorem measurable_cumulativeObservation (n : ℕ) :
    Measurable (@cumulativeObservation n) := by
  apply Measurable.of_eval
  intro k
  apply Finset.measurable_sum
  intro i hi
  by_cases h : i.val < k.val
  · simpa only [ite_eq_left h] using measurable_pi_apply i
  · simp only [ite_eq_right h]
    exact measurable_const

@[simp] theorem cumulativeObservation_last {n : ℕ} (x : Fin n → ℝ) :
    cumulativeObservation x (Fin.last n) = ∑ i, x i := by
  simp [cumulativeObservation, Fin.is_lt]

@[simp] theorem cumulativeObservation_zero {n : ℕ} (x : Fin n → ℝ) :
    cumulativeObservation x 0 = 0 := by
  simp [cumulativeObservation]

theorem gaussianSkeleton_signal_withDensity {n : ℕ}
    (t : Fin n → ℝ≥0) (s : ℝ) :
    Measure.map cumulativeObservation
        (Measure.pi (fun i => gaussianReal ((t i : ℝ) * s) (t i))) =
      (Measure.map cumulativeObservation
        (Measure.pi (fun i => gaussianReal 0 (t i)))).withDensity
        (fun y => ENNReal.ofReal
          (gaussianSignalLikelihood (∑ i, t i) s (y (Fin.last n)))) := by
  rw [gaussianIncrements_signal_withDensity]
  have h := map_withDensity_comp_observation
    (Measure.pi (fun i : Fin n => gaussianReal 0 (t i)))
    (@cumulativeObservation n) (measurable_cumulativeObservation n)
    (fun y : Fin (n + 1) → ℝ => ENNReal.ofReal
      (gaussianSignalLikelihood (∑ i, t i) s (y (Fin.last n))))
    (by unfold gaussianSignalLikelihood; fun_prop)
  simpa only [Function.comp_def, cumulativeObservation_last] using h

def cumulativeVectorObservation {V : Type*} {n : ℕ}
    (x : V × Fin n → ℝ) (v : V) : Fin (n + 1) → ℝ :=
  cumulativeObservation (fun i => x (v, i))

theorem measurable_cumulativeVectorObservation (V : Type*) (n : ℕ) :
    Measurable (@cumulativeVectorObservation V n) := by
  apply Measurable.of_eval
  intro v
  exact (measurable_cumulativeObservation n).comp (by fun_prop)

@[simp] theorem cumulativeVectorObservation_last {V : Type*} {n : ℕ}
    (x : V × Fin n → ℝ) (v : V) :
    cumulativeVectorObservation x v (Fin.last n) = ∑ i, x (v, i) :=
  cumulativeObservation_last _

theorem gaussianChannelIncrement_exponent {V : Type*} [Fintype V] {n : ℕ}
    (t : Fin n → ℝ≥0) (s : V → ℝ) (x : V × Fin n → ℝ) :
    (∑ p : V × Fin n, (s p.1 * x p - (t p.2 : ℝ) * s p.1 ^ 2 / 2)) =
      (∑ v, s v * cumulativeVectorObservation x v (Fin.last n)) -
        ((∑ i, t i : ℝ≥0) : ℝ) / 2 * ∑ v, s v ^ 2 := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [cumulativeVectorObservation_last, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_mul, NNReal.coe_sum]
  ring

theorem gaussianVectorSkeleton_signal_withDensity
    {V : Type*} [Fintype V] {n : ℕ} (t : Fin n → ℝ≥0) (s : V → ℝ) :
    Measure.map cumulativeVectorObservation
        (Measure.pi (fun p : V × Fin n => gaussianReal ((t p.2 : ℝ) * s p.1) (t p.2))) =
      (Measure.map cumulativeVectorObservation
        (Measure.pi (fun p : V × Fin n => gaussianReal 0 (t p.2)))).withDensity
        (fun y => ENNReal.ofReal
          (gaussianVectorLikelihood (∑ i, t i) s (fun v => y v (Fin.last n)))) := by
  rw [gaussianPi_variable_signal_withDensity]
  have h := map_withDensity_comp_observation
    (Measure.pi (fun p : V × Fin n => gaussianReal 0 (t p.2)))
    (@cumulativeVectorObservation V n) (measurable_cumulativeVectorObservation V n)
    (fun y : V → Fin (n + 1) → ℝ => ENNReal.ofReal
      (gaussianVectorLikelihood (∑ i, t i) s (fun v => y v (Fin.last n))))
    (by unfold gaussianVectorLikelihood; fun_prop)
  simpa only [Function.comp_def, gaussianVectorLikelihood,
    gaussianChannelIncrement_exponent] using h

theorem gaussianVectorSkeleton_spin_withDensity
    {V : Type*} [Fintype V] {n : ℕ} (t : Fin n → ℝ≥0) (s : V → ℝ)
    (hs : ∀ v, s v ^ 2 = 1) :
    Measure.map cumulativeVectorObservation
        (Measure.pi (fun p : V × Fin n => gaussianReal ((t p.2 : ℝ) * s p.1) (t p.2))) =
      (Measure.map cumulativeVectorObservation
        (Measure.pi (fun p : V × Fin n => gaussianReal 0 (t p.2)))).withDensity
        (fun y => ENNReal.ofReal
          (Real.exp ((∑ v, s v * y v (Fin.last n)) -
            ((∑ i, t i : ℝ≥0) : ℝ) * Fintype.card V / 2))) := by
  simpa only [gaussianVectorLikelihood_of_sq_eq_one _ _ _ hs] using
    gaussianVectorSkeleton_signal_withDensity t s

end Problem367

end

end OAI
