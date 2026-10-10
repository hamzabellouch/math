import OAI.Geometry.RCD.Heat.QuadraticHeatBochnerMass
import OAI.Geometry.RCD.Metric.RadonDensityL2Bound

namespace OAI

/-! # A vanishing full shifted source controls its nonnegative local density -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
theorem weighted_nonnegative_inner_mass_tendsto_zero
    (w : X → ℝ) (c : ℕ → X → ℝ) {S : Set X} (hS : MeasurableSet S)
    (hI : ∀ k, Integrable (fun x => w x*c k x) μ)
    (hpos : ∀ k, ∀ᵐ x ∂μ, 0 ≤ w x*c k x)
    (hone : ∀ x∈S, w x=1)
    (hlim : Tendsto (fun k => ∫ x, w x*c k x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x in S, c k x ∂μ) atTop (𝓝 0) := by
  have he k : (fun x => w x*c k x) =ᵐ[μ.restrict S] c k := by
    filter_upwards [ae_restrict_mem hS] with x hx
    rw [hone x hx,one_mul]
  apply squeeze_zero (fun k => ?_) (fun k => ?_) hlim
  · rw [← integral_congr_ae (he k)]
    exact integral_nonneg_of_ae (ae_restrict_of_ae (hpos k))
  · rw [← integral_congr_ae (he k)]
    exact integral_mono_measure Measure.restrict_le_self (hpos k) (hI k)

omit [IsFiniteMeasureOnCompacts μ] in
theorem GoodLaplacianCutoff.weighted_radon_le_full
    {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (σ : Measure X) [IsFiniteMeasure σ] :
    (∫ x, χ.weight x*(σ.rnDeriv μ x).toReal ∂μ) ≤ ∫ x, χ.weight x ∂σ := by
  have hi : Integrable χ.weight σ :=
    χ.weight.continuous.integrable_of_hasCompactSupport (χ.hasCompactSupport μ Q)
  have h := integral_mono_measure (Measure.withDensity_rnDeriv_le σ μ)
    (Eventually.of_forall fun x => (χ.bounds x).1) hi
  rw [integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv σ μ)
    (Measure.rnDeriv_lt_top σ μ) χ.weight] at h
  simpa only [smul_eq_mul,mul_comm] using h

theorem GoodLaplacianCutoff.shifted_density_integrable
    {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (σ : Measure X) [IsFiniteMeasure σ] (d : Lp ℝ 2 μ) (n : ℝ) :
    Integrable (fun x => χ.weight x*((σ.rnDeriv μ x).toReal-2*d x+n)) μ := by
  have hχ : Integrable χ.weight μ :=
    χ.weight.continuous.integrable_of_hasCompactSupport (χ.hasCompactSupport μ Q)
  have hd : Integrable (fun x => χ.weight x*d x) μ := by
    have hi := (Lp.memLp (SobolevSpace.toLp μ Q χ.sobolev)).integrable_mul (Lp.memLp d)
    exact hi.congr (χ.representative.mono fun x hx => by
      change SobolevSpace.toLp μ Q χ.sobolev x*d x=χ.weight x*d x
      rw [hx])
  have hRN : Integrable (fun x => χ.weight x*(σ.rnDeriv μ x).toReal) μ := by
    have hi : Integrable (fun x => (σ.rnDeriv μ x).toReal) μ := by
      simpa only [IntegrableOn,Measure.restrict_univ] using
        (Measure.integrableOn_toReal_rnDeriv (μ := σ) (ν := μ) (s := univ) (measure_ne_top _ _))
    exact hi.bdd_mul χ.weight.continuous.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (χ.bounds x).1]
      exact (χ.bounds x).2)
  convert (hRN.sub (hd.const_mul 2)).add (hχ.const_mul n) using 1
  funext x
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

theorem GoodLaplacianCutoff.shifted_density_tendsto_zero
    {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (σ : ℕ → Measure X) [∀ k, IsFiniteMeasure (σ k)]
    (d : ℕ → Lp ℝ 2 μ) (n : ℝ)
    (hpos : ∀ k, ∀ᵐ x ∂μ.restrict (closedBall p (2*r)),
      0 ≤ ((σ k).rnDeriv μ x).toReal-2*d k x+n)
    (hlim : Tendsto (fun k => (∫ x, χ.weight x ∂σ k)-
      2*(∫ x, χ.weight x*d k x ∂μ)+n*(∫ x, χ.weight x ∂μ)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, χ.weight x*(((σ k).rnDeriv μ x).toReal-2*d k x+n) ∂μ)
      atTop (𝓝 0) := by
  have hχ : Integrable χ.weight μ :=
    χ.weight.continuous.integrable_of_hasCompactSupport (χ.hasCompactSupport μ Q)
  have hχd k : Integrable (fun x => χ.weight x*d k x) μ := by
    have hi := (Lp.memLp (SobolevSpace.toLp μ Q χ.sobolev)).integrable_mul (Lp.memLp (d k))
    exact hi.congr (χ.representative.mono fun x hx => by
      change SobolevSpace.toLp μ Q χ.sobolev x*d k x=χ.weight x*d k x
      rw [hx])
  have hχRN k : Integrable (fun x => χ.weight x*((σ k).rnDeriv μ x).toReal) μ := by
    have hi : Integrable (fun x => ((σ k).rnDeriv μ x).toReal) μ := by
      simpa only [IntegrableOn,Measure.restrict_univ] using
        (Measure.integrableOn_toReal_rnDeriv (μ := σ k) (ν := μ) (s := univ) (measure_ne_top _ _))
    exact hi.bdd_mul χ.weight.continuous.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (χ.bounds x).1]
      exact (χ.bounds x).2)
  have hn k : ∀ᵐ x ∂μ, 0 ≤ χ.weight x*(((σ k).rnDeriv μ x).toReal-2*d k x+n) := by
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).mp (hpos k)] with x hx
    by_cases hm : x∈closedBall p (2*r)
    · exact mul_nonneg (χ.bounds x).1 (hx hm)
    · rw [χ.zero x (lt_of_not_ge (by simpa only [mem_closedBall,dist_comm] using hm)),zero_mul]
  apply squeeze_zero (fun k => integral_nonneg_of_ae (hn k)) (fun k => ?_) hlim
  have hfun : (fun x => χ.weight x*(((σ k).rnDeriv μ x).toReal-2*d k x+n)) =
      fun x => χ.weight x*((σ k).rnDeriv μ x).toReal-2*(χ.weight x*d k x)+n*χ.weight x := by
    funext x
    ring
  have ha := integral_add ((hχRN k).sub ((hχd k).const_mul 2)) (hχ.const_mul n)
  have hs := integral_sub (hχRN k) ((hχd k).const_mul 2)
  simp only [Pi.sub_apply] at ha
  rw [hfun,ha,hs,integral_const_mul,integral_const_mul]
  linarith only [χ.weighted_radon_le_full μ Q (σ k)]

end RegularPointCoordinates

end

end OAI
