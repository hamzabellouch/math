import OAI.MeasureTheory.Falconer.Fourier.FiberSchwartz

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace

noncomputable def sourceDensityMeasure (a : Plane → ℝ) : Measure Plane :=
  volume.withDensity (fun x => ENNReal.ofReal (a x))

theorem sourceDensityMeasure_finite (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : Continuous a) (hn : ∀ x, 0 ≤ a x) : IsFiniteMeasure (sourceDensityMeasure a) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (ha.integrable_of_hasCompactSupport hc)
    (Filter.Eventually.of_forall hn)]
  exact ENNReal.ofReal_ne_top

theorem sourceSchwartzFiber_measure (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x) (θ : ℝ) :
    projectedMeasure (sourceDensityMeasure a) θ =
      volume.withDensity (fun z => ENNReal.ofReal (sourceSchwartzFiber a hc ha θ z)) := by
  rw [sourceDensityMeasure,projectedMeasure_withDensity _ ha.continuous.measurable.ennreal_ofReal]
  congr 1
  funext z
  exact (sourceSchwartzFiber_density a hc ha hn θ z).symm

theorem schwartz_density_fourier (f : 𝓢(ℝ, ℝ)) (hf : ∀ z, 0 ≤ f z) (ξ : ℝ) :
    (𝓕 (complexSchwartz f)) ξ =
      sourceFourier (volume.withDensity (fun z => ENNReal.ofReal (f z))) ξ := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [sourceFourier,charFun_apply]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with z
  rw [ENNReal.toReal_ofReal (hf z)]
  change Complex.exp _ * (f z : ℂ) = (f z : ℂ) * Complex.exp _
  rw [mul_comm]
  congr 2
  simp only [Real.inner_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  ring

theorem sourceSchwartzFiber_fourier (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x) (θ ξ : ℝ) :
    (𝓕 (complexSchwartz (sourceSchwartzFiber a hc ha θ))) ξ =
      sourceFourier (sourceDensityMeasure a) (ξ • sourceNormal θ) := by
  let := sourceDensityMeasure_finite a hc ha.continuous hn
  rw [schwartz_density_fourier _ (sourceSchwartzFiber_nonneg a hc ha hn θ),
    ← sourceSchwartzFiber_measure a hc ha hn θ,source_fourier_slice]

theorem sourceSchwartzFiber_sliceEnergy (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x) (θ s : ℝ) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal
      (‖(𝓕 (complexSchwartz (sourceSchwartzFiber a hc ha θ))) ξ‖^2 * |ξ|^(s-1))) =
        sourceSliceEnergy (sourceDensityMeasure a) s θ := by
  simp_rw [sourceSchwartzFiber_fourier a hc ha hn θ]
  apply lintegral_congr
  intro ξ
  exact ENNReal.ofReal_mul (sq_nonneg _)

end PlanarFalconer

end OAI
