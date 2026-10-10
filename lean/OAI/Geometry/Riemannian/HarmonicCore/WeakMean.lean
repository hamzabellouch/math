import OAI.Geometry.Riemannian.HarmonicCore.SphericalMean
import OAI.Geometry.Riemannian.HarmonicCore.MetricLaplacian
import OAI.Geometry.Riemannian.HarmonicCore.PolarMetric
import OAI.Geometry.Riemannian.HarmonicCore.MaximumPrinciple
import OAI.Geometry.Riemannian.HarmonicCore.PolarDensity

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution
open Matrix
open scoped RealInnerProductSpace

namespace HarmonicCounterexample.Main.SmoothMetric3

lemma radial_inverse (g : SmoothMetric3) (x : E3)
    (hr : g.coeff x *ᵥ x.ofLp = x.ofLp) :
    (g.coeff x)⁻¹ *ᵥ x.ofLp = x.ofLp := by
  calc
    _ = (g.coeff x)⁻¹ *ᵥ (g.coeff x *ᵥ x.ofLp) := congrArg _ hr.symm
    _ = x.ofLp := by
      rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (g.positive x).det_pos.ne'),Matrix.one_mulVec]



lemma radial_metricFlux (g : SmoothMetric3) (u : E3 → ℝ) (x : E3)
    (hr : g.coeff x *ᵥ x.ofLp = x.ofLp) :
    (∑ i, x i * g.metricFlux u x i) =
      Real.sqrt (g.coeff x).det * fderiv ℝ u x x := by
  have hi := g.radial_inverse x hr
  have hcoord (j : Fin 3) : (∑ i, x i * (g.coeff x)⁻¹ i j) = x j := by
    have h := congrFun hi j
    simpa only [Matrix.mulVec,dotProduct,g.inverse_symmetric x,mul_comm] using h
  calc
    _ = Real.sqrt (g.coeff x).det *
        ∑ j, (∑ i, x i * (g.coeff x)⁻¹ i j) * coordDeriv u j x := by
      simp only [metricFlux,energyMatrix,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = Real.sqrt (g.coeff x).det * ∑ j, x j * coordDeriv u j x := by simp_rw [hcoord]
    _ = _ := by
      congr 1
      simpa only [map_sum,map_smul,smul_eq_mul,coordDeriv] using
        congrArg (fderiv ℝ u x) (coordinate_expansion x)



lemma radial_square_test_derivative {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (x : E3) (i : Fin 3) :
    coordDeriv (fun y : E3 ↦ ψ (‖y‖^2)) i x = 2 * deriv ψ (‖x‖^2) * x i := by
  have hh := (hψ.differentiable (by simp) (‖x‖^2)).hasDerivAt.comp_hasFDerivAt x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have he : fderiv ℝ (fun y : E3 ↦ ψ (‖y‖^2)) x =
      deriv ψ (‖x‖^2) • 2 • innerSL ℝ x := by convert! hh.fderiv
  unfold coordDeriv
  rw [he]
  simp [innerSL_apply_apply,coordinateVector,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct]
  ring



lemma radial_square_test_support {ψ : ℝ → ℝ} {R : ℝ} (hR : 0<R)
    (hψs : tsupport ψ ⊆ Iio (R^2)) :
    tsupport (fun x : E3 ↦ ψ (‖x‖^2)) ⊆ Metric.ball (0:E3) R := by
  intro x hx
  have hp := tsupport_comp_subset_preimage ψ (continuous_norm.pow 2) hx
  have hh := hψs hp
  change ‖x‖^2 < R^2 at hh
  simp only [Metric.mem_ball,dist_zero_right]
  have hn := norm_nonneg x
  nlinarith



lemma radial_square_test_compact {ψ : ℝ → ℝ} {R : ℝ} (hR : 0<R)
    (hψs : tsupport ψ ⊆ Iio (R^2)) :
    HasCompactSupport (fun x : E3 ↦ ψ (‖x‖^2)) :=
  (isCompact_closedBall (0:E3) R).of_isClosed_subset (isClosed_tsupport _)
    ((radial_square_test_support hR hψs).trans Metric.ball_subset_closedBall)



lemma radial_square_test_green (g : SmoothMetric3) {R : ℝ} (hR : 0<R)
    {u : E3 → ℝ} (hu : ContDiff ℝ ∞ u)
    (hharm : ∀ x ∈ Metric.ball (0:E3) R, g.laplacian u x=0)
    (hrad : ∀ x : E3, g.coeff x *ᵥ x.ofLp=x.ofLp)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : tsupport ψ ⊆ Iio (R^2)) :
    (∫ x : E3, 2 * deriv ψ (‖x‖^2) *
      Real.sqrt (g.coeff x).det * fderiv ℝ u x x) = 0 := by
  have ht : ContDiff ℝ ∞ (fun x : E3 ↦ ψ (‖x‖^2)) := hψ.comp (contDiff_id.norm_sq ℝ)
  have hc := radial_square_test_compact hR hψs
  have hg := g.laplacian_green hu ht hc
  have hz : (∫ x : E3, ψ (‖x‖^2) * (Real.sqrt (g.coeff x).det * g.laplacian u x))=0 := by
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun x ↦ by
      change ψ (‖x‖^2) * (Real.sqrt (g.coeff x).det * g.laplacian u x) = 0
      by_cases hx : x ∈ Metric.ball (0:E3) R
      · rw [hharm x hx,mul_zero,mul_zero]
      · have ht := notMem_subset (radial_square_test_support hR hψs) hx
        rw [image_eq_zero_of_notMem_tsupport ht,zero_mul]
  rw [hz] at hg
  have he : (fun x : E3 ↦ ∑ i,coordDeriv (fun y : E3 ↦ ψ (‖y‖^2)) i x * g.metricFlux u x i) =
      (fun x ↦ 2 * deriv ψ (‖x‖^2) * Real.sqrt (g.coeff x).det * fderiv ℝ u x x) := by
    funext x
    simp_rw [radial_square_test_derivative hψ]
    calc
      _ = (2 * deriv ψ (‖x‖^2)) * (∑ i, x i * g.metricFlux u x i) := by rw [Finset.mul_sum]; congr 1; simp only [mul_assoc]
      _ = _ := by rw [g.radial_metricFlux u x (hrad x)]; ring
  rw [he] at hg
  linarith

end HarmonicCounterexample.Main.SmoothMetric3

namespace HarmonicCounterexample.Main

lemma integral_angular_normalization (v : UnitSphere3 → ℝ) :
    (∫ z : UnitSphere3, v z ∂(volume : Measure E3).toSphere) =
      (4*Real.pi) * (∫ z : UnitSphere3, v z ∂angularMeasure) := by
  rw [angularMeasure,integral_smul_measure,ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul]
  field_simp

end HarmonicCounterexample.Main

namespace HarmonicCounterexample.Main.SmoothMetric3

lemma radial_square_test_integrable (g : SmoothMetric3) {R : ℝ} (hR : 0<R)
    {u : E3 → ℝ} (hu : ContDiff ℝ ∞ u) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : tsupport ψ ⊆ Set.Iio (R^2)) :
    Integrable (fun x : E3 ↦ 2 * deriv ψ (‖x‖^2) *
      Real.sqrt (g.coeff x).det * fderiv ℝ u x x) := by
  have hdc : Continuous (fun x : E3 ↦ deriv ψ (‖x‖^2)) :=
    (hψ.deriv' (n:=∞)).continuous.comp (continuous_norm.pow 2)
  have hdf : Continuous (fun x : E3 ↦ fderiv ℝ u x x) :=
    (hu.continuous_fderiv (by simp)).clm_apply continuous_id
  have hc := radial_square_test_compact hR (tsupport_deriv_subset.trans hψs)
  exact (((continuous_const.mul hdc).mul (g.density_continuous)).mul hdf).integrable_of_hasCompactSupport
    ((hc.mul_left).mul_right.mul_right)

end HarmonicCounterexample.Main.SmoothMetric3

namespace HarmonicCounterexample.Main

theorem polar_harmonic_weak_mean {a R : ℝ} (ha : 0<a) (hR : 0<R)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r≤1 → f r=r)
    (hb : ∀ r : ℝ, 0≤r → a*r≤ f r ∧ f r≤r)
    {u : E3 → ℝ} (hu : ContDiff ℝ ∞ u)
    (hharm : ∀ x ∈ Metric.ball (0:E3) R,
      (polarMetric ha f H hs hc hb).laplacian u x=0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Iio (R^2)) :
    (∫ r in Ioi (0:ℝ), 2*r*deriv ψ (r^2)*f r^2*sphericalMeanDerivative u r)=0 := by
  let g := polarMetric ha f H hs hc hb
  let v : E3 → ℝ := fun x ↦ 2 * deriv ψ (‖x‖^2) *
    Real.sqrt (g.coeff x).det * fderiv ℝ u x x
  have hv : Integrable v := g.radial_square_test_integrable hR hu hψ hψs
  have hz : (∫ x : E3, v x) = 0 :=
    g.radial_square_test_green hR hu hharm (polarCoeff_radial f H) hψ hψs
  have hpolar := integral_polar_three hv
  have hpoint (r : ℝ) (hr : 0<r) :
      r^2 * (∫ z : UnitSphere3, v (r • (z:E3)) ∂(volume : Measure E3).toSphere) =
        (4*Real.pi) * (2*r*deriv ψ (r^2)*f r^2*sphericalMeanDerivative u r) := by
    rw [integral_angular_normalization]
    have he : (∫ z : UnitSphere3, v (r • (z:E3)) ∂angularMeasure) =
        (2*deriv ψ (r^2)*(f r/r)^2*r)*sphericalMeanDerivative u r := by
      rw [sphericalMeanDerivative,← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun z ↦ by
        have hn : ‖(z:E3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using z.property
        have hnr : ‖r • (z:E3)‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hn,mul_one]
        have hne : r • (z:E3) ≠ 0 := by
          intro hz
          rw [hz,norm_zero] at hnr
          linarith
        change v (r • (z:E3)) = _
        dsimp only [v,g]
        rw [polarMetric_density,ite_eq_right hne,hnr,map_smul,smul_eq_mul]
        ring
    rw [he]
    field_simp
  have hi : (∫ x : E3, v x) =
      (4*Real.pi) * (∫ r in Ioi (0:ℝ), 2*r*deriv ψ (r^2)*f r^2*sphericalMeanDerivative u r) := by
    rw [hpolar,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    exact hpoint r hr
  rw [hz] at hi
  exact (mul_eq_zero.mp hi.symm).resolve_left (mul_ne_zero (by norm_num) Real.pi_ne_zero)

end HarmonicCounterexample.Main

end

end OAI
