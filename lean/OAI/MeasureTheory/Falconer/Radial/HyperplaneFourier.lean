import OAI.MeasureTheory.Falconer.Radial.HyperplaneFiber

namespace OAI

/-! The Fourier slice identity for the fixed hyperplane fiber. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal SchwartzMap FourierTransform

noncomputable def euclideanDensityMeasure {n : ℕ} (a : Space n → ℝ) : Measure (Space n) :=
  volume.withDensity (fun x => ENNReal.ofReal (a x))

theorem euclideanDensityMeasure_finite {n : ℕ} (a : Space n → ℝ)
    (hc : HasCompactSupport a) (ha : Continuous a) (hn : ∀ x, 0 ≤ a x) :
    IsFiniteMeasure (euclideanDensityMeasure a) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (ha.integrable_of_hasCompactSupport hc)
    (Filter.Eventually.of_forall hn)]
  exact ENNReal.ofReal_ne_top

theorem hyperplaneProjection_inner {n : ℕ} (w : Sphere (n+1)) (x : Space (n+1))
    (ξ : Space n) :
    inner ℝ (hyperplaneProjection w x) ξ = inner ℝ x (hyperplaneSliceEmbedding w ξ) := by
  nth_rw 2 [← hyperplaneFrame_reconstruct w x]
  change _ = inner ℝ ((northRotation w).symm (coordinateJoin (hyperplaneProjection w x) _))
    ((northRotation w).symm (coordinateJoin ξ 0))
  rw [(northRotation w).symm.inner_map_map, coordinateJoin_inner]
  simp

theorem hyperplane_source_fourier_slice {n : ℕ} (μ : Measure (Space (n+1)))
    [IsFiniteMeasure μ] (w : Sphere (n+1)) (ξ : Space n) :
    sourceFourier (hyperplaneCoordinateMeasure μ w) ξ =
      sourceFourier μ (hyperplaneSliceEmbedding w ξ) := by
  simp only [sourceFourier, charFun_apply, hyperplaneCoordinateMeasure]
  rw [integral_map (contDiff_hyperplaneProjection w).continuous.measurable.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  rw [inner_smul_right, inner_smul_right, hyperplaneProjection_inner]

theorem euclidean_schwartz_density_fourier {n : ℕ} (f : 𝓢(Space n, ℝ))
    (hf : ∀ x, 0 ≤ f x) (ξ : Space n) :
    𝓕 (euclideanComplexSchwartz f) ξ =
      sourceFourier (euclideanDensityMeasure (fun x => f x)) ξ := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [sourceFourier, charFun_apply, euclideanDensityMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (hf x)]
  change Complex.exp _ * (f x : ℂ) = (f x : ℂ) * Complex.exp _
  rw [mul_comm]
  congr 2
  simp only [inner_smul_right, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  ring

theorem hyperplaneSchwartzFiber_measure {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (w : Sphere (n+1)) :
    hyperplaneCoordinateMeasure (euclideanDensityMeasure a) w =
      euclideanDensityMeasure (fun y => hyperplaneSchwartzFiber a hc ha w y) := by
  rw [euclideanDensityMeasure, hyperplaneCoordinateMeasure_withDensity _
    ha.continuous.measurable.ennreal_ofReal]
  congr 1
  funext y
  exact (hyperplaneSchwartzFiber_density a hc ha hn w y).symm

theorem hyperplaneSchwartzFiber_fourier {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (w : Sphere (n+1)) (ξ : Space n) :
    𝓕 (euclideanComplexSchwartz (hyperplaneSchwartzFiber a hc ha w)) ξ =
      sourceFourier (euclideanDensityMeasure a) (hyperplaneSliceEmbedding w ξ) := by
  let := euclideanDensityMeasure_finite a hc ha.continuous hn
  rw [euclidean_schwartz_density_fourier _ (hyperplaneSchwartzFiber_nonneg a hc ha hn w),
    ← hyperplaneSchwartzFiber_measure a hc ha hn w, hyperplane_source_fourier_slice]

theorem hyperplaneSchwartzFiber_energy {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (w : Sphere (n+1)) (s : ℝ) :
    (∫⁻ ξ : Space n, ENNReal.ofReal
      (‖𝓕 (euclideanComplexSchwartz (hyperplaneSchwartzFiber a hc ha w)) ξ‖^2 *
        ‖ξ‖^(s-n))) = hyperplaneFourierEnergy (euclideanDensityMeasure a) s w := by
  simp only [hyperplaneSchwartzFiber_fourier a hc ha hn w, hyperplaneFourierEnergy_formula]

end Falconer

end OAI
