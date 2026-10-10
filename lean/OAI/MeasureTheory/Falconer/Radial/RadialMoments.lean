import OAI.MeasureTheory.Falconer.Angular.IntegerCaps
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

namespace OAI

/-!
# From radial projection moments to integer cap availability

The radial pushforwards form a Markov kernel. Mathlib's kernel
Radon--Nikodym derivative supplies a jointly measurable version of all
their angular densities, so separate choices of densities are unnecessary.
This connects the published radial-moment input to the truncation step.
-/

namespace Falconer
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-- The radial projection law, with the pin as its kernel parameter. -/
noncomputable def radialKernel {d : ℕ} (ν : ProbabilityMeasure (Space d)) :
    Kernel (Space d) (Space d) :=
  ((Kernel.id : Kernel (Space d) (Space d)) ×ₖ
    Kernel.const (Space d) (ν : Measure (Space d))).map
      (fun z : Space d × Space d => radialDirection z.1 z.2)

instance {d : ℕ} (ν : ProbabilityMeasure (Space d)) : IsMarkovKernel (radialKernel ν) := by
  unfold radialKernel
  exact Kernel.IsMarkovKernel.map _ measurable_radialDirection_joint

theorem radialKernel_apply {d : ℕ} (ν : ProbabilityMeasure (Space d)) (x : Space d) :
    radialKernel ν x = (ν : Measure (Space d)).map (radialDirection x) := by
  have hr : Measurable (radialDirection x) := by
    unfold radialDirection
    fun_prop
  ext S hS
  rw [radialKernel, Kernel.map_apply' _ measurable_radialDirection_joint _ hS,
    Kernel.id_prod_apply' _ _ (hS.preimage measurable_radialDirection_joint),
    Kernel.const_apply, Measure.map_apply hr hS]
  rfl

/-- A single jointly measurable choice of the radial angular densities. -/
noncomputable def radialKernelDensity {d : ℕ} (ν : ProbabilityMeasure (Space d))
    (σ : Measure (Space d)) : Space d × Space d → ℝ≥0∞ :=
  fun z => (radialKernel ν).rnDeriv (Kernel.const (Space d) σ) z.1 z.2

@[fun_prop] theorem measurable_radialKernelDensity {d : ℕ}
    (ν : ProbabilityMeasure (Space d)) (σ : Measure (Space d)) :
    Measurable (radialKernelDensity ν σ) :=
  Kernel.measurable_rnDeriv _ _

theorem radialKernelDensity_withDensity {d : ℕ} (ν : ProbabilityMeasure (Space d))
    (σ : Measure (Space d)) [IsFiniteMeasure σ] (x : Space d)
    (h : (ν : Measure (Space d)).map (radialDirection x) ≪ σ) :
    (ν : Measure (Space d)).map (radialDirection x) =
      σ.withDensity (fun a => radialKernelDensity ν σ (x, a)) := by
  have hker : radialKernel ν x ≪ Kernel.const (Space d) σ x := by
    simpa only [radialKernel_apply, Kernel.const_apply] using h
  have heq := Kernel.withDensity_rnDeriv_eq hker
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv _ _),
    Kernel.const_apply, radialKernel_apply] at heq
  exact heq.symm

theorem radialKernelDensity_moment {d : ℕ} (ν : ProbabilityMeasure (Space d))
    (σ : Measure (Space d)) [IsFiniteMeasure σ] (x : Space d) (p : ℝ) :
    (∫⁻ a, radialKernelDensity ν σ (x, a) ^ p ∂σ) =
      ∫⁻ a, ((ν : Measure (Space d)).map (radialDirection x)).rnDeriv σ a ^ p ∂σ := by
  apply lintegral_congr_ae
  have heq := Kernel.rnDeriv_eq_rnDeriv_measure (κ := radialKernel ν)
    (η := Kernel.const (Space d) σ) (a := x)
  simp only [Kernel.const_apply, radialKernel_apply] at heq
  filter_upwards [heq] with a ha
  exact congrArg (fun t : ℝ≥0∞ => t ^ p) ha

/-- The moment written as an integral of the density agrees with the
published convention of taking the `p`th power of its `Lᵖ` norm. -/
theorem radial_rnDeriv_moment_eq_norm {d : ℕ} (ν : ProbabilityMeasure (Space d))
    (σ : Measure (Space d)) [IsFiniteMeasure σ] (x : Space d)
    {p : ℝ} (hp : 0 < p) :
    (∫⁻ a, ((ν : Measure (Space d)).map (radialDirection x)).rnDeriv σ a ^ p ∂σ) =
      (eLpNorm (fun a => (((ν : Measure (Space d)).map
        (radialDirection x)).rnDeriv σ a).toReal) (ENNReal.ofReal p) σ) ^ p := by
  let γ := (ν : Measure (Space d)).map (radialDirection x)
  have hγ : IsFiniteMeasure γ := by
    dsimp [γ]
    infer_instance
  have hm : Measurable (γ.rnDeriv σ) := Measure.measurable_rnDeriv γ σ
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top hm.ennreal_toReal.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_lt_top γ σ] with a ha
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal ha.ne]

/-- A.e. absolute continuity and integrated radial `p`th moments imply the
integer cap conclusion. These are precisely the density data used from
the radial projection input; the geometric cap bound on `σ` is explicit. -/
theorem capAvailable_of_radial_moments {d : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (σ : Measure (Space d)) [IsFiniteMeasure σ]
    (hν : ∀ᵐ x ∂(μ : Measure (Space d)),
      (ν : Measure (Space d)).map (radialDirection x) ≪ σ)
    (hμ : ∀ᵐ y ∂(ν : Measure (Space d)),
      (μ : Measure (Space d)).map (radialDirection y) ≪ σ)
    {p q A : ℝ} (hp : 1 < p) (hA : 0 < A)
    (hσ : ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      σ (Metric.ball w u) ≤ ENNReal.ofReal (A * u ^ q))
    (hmoment : ((∫⁻ x, ∫⁻ a,
      ((ν : Measure (Space d)).map (radialDirection x)).rnDeriv σ a ^ p ∂σ
        ∂(μ : Measure (Space d))) +
      ∫⁻ y, ∫⁻ a,
        ((μ : Measure (Space d)).map (radialDirection y)).rnDeriv σ a ^ p ∂σ
          ∂(ν : Measure (Space d))) ≠ ∞)
    (Γ : ℕ → Set (Space d × Space d)) (hΓ : ∀ N, MeasurableSet (Γ N)) :
    CapAvailable μ ν Γ q := by
  apply capAvailable_of_bilateral_radial_densities_restrict μ ν σ
    (radialKernelDensity ν σ) (radialKernelDensity μ σ)
    (measurable_radialKernelDensity ν σ) (measurable_radialKernelDensity μ σ)
    _ _ hp hA hσ _ Γ hΓ
  · filter_upwards [hν] with x hx
    exact radialKernelDensity_withDensity ν σ x hx
  · filter_upwards [hμ] with y hy
    exact radialKernelDensity_withDensity μ σ y hy
  · simpa only [radialKernelDensity_moment] using hmoment

/-- The same consequence in the integrated `Lᵖ` norm notation of the
published radial projection estimate. -/
theorem capAvailable_of_radial_Lp_moments {d : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (σ : Measure (Space d)) [IsFiniteMeasure σ]
    (hν : ∀ᵐ x ∂(μ : Measure (Space d)),
      (ν : Measure (Space d)).map (radialDirection x) ≪ σ)
    (hμ : ∀ᵐ y ∂(ν : Measure (Space d)),
      (μ : Measure (Space d)).map (radialDirection y) ≪ σ)
    {p q A : ℝ} (hp : 1 < p) (hA : 0 < A)
    (hσ : ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      σ (Metric.ball w u) ≤ ENNReal.ofReal (A * u ^ q))
    (hmoment : ((∫⁻ x,
      (eLpNorm (fun a => (((ν : Measure (Space d)).map
        (radialDirection x)).rnDeriv σ a).toReal) (ENNReal.ofReal p) σ) ^ p
          ∂(μ : Measure (Space d))) +
      ∫⁻ y, (eLpNorm (fun a => (((μ : Measure (Space d)).map
        (radialDirection y)).rnDeriv σ a).toReal) (ENNReal.ofReal p) σ) ^ p
          ∂(ν : Measure (Space d))) ≠ ∞)
    (Γ : ℕ → Set (Space d × Space d)) (hΓ : ∀ N, MeasurableSet (Γ N)) :
    CapAvailable μ ν Γ q := by
  apply capAvailable_of_radial_moments μ ν σ hν hμ hp hA hσ _ Γ hΓ
  simpa only [radial_rnDeriv_moment_eq_norm _ _ _ (zero_lt_one.trans hp)] using hmoment

end Falconer

end OAI
