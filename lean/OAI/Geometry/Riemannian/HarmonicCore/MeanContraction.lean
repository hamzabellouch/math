import OAI.Geometry.Riemannian.HarmonicCore.HarmonicMean

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

namespace HarmonicCounterexample.Main

lemma continuous_sphere_restriction {R r : ℝ} (hr : r ∈ Icc (0:ℝ) R)
    {u : E3 → ℝ} (hu : ContinuousOn u (Metric.closedBall (0:E3) R)) :
    Continuous (fun z : UnitSphere3 ↦ u (r • (z:E3))) := by
  let e : UnitSphere3 → Metric.closedBall (0:E3) R := fun z ↦ ⟨r • (z:E3),by
    have hz : ‖(z:E3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using z.property
    simpa only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg hr.1,hz,mul_one] using hr.2⟩
  exact hu.domRestrict.comp (show Continuous e by dsimp [e]; fun_prop)

theorem polar_dirichlet_L2_contraction {a R : ℝ} (ha : 0<a) (hR : 0<R)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r≤1 → f r=r)
    (hb : ∀ r : ℝ, 0≤r → a*r≤ f r ∧ f r≤r)
    (F : SmoothMetric3.CompactSmoothData) {r : ℝ} (hr : r ∈ Icc (0:ℝ) R) :
    (∫ z : UnitSphere3, ((polarMetric ha f H hs hc hb).classicalExtension R hR F
      (r • (z:E3)))^2 ∂angularMeasure) ≤
    ∫ z : UnitSphere3, ((F:E3 → ℝ) (R • (z:E3)))^2 ∂angularMeasure := by
  let g := polarMetric ha f H hs hc hb
  let Q := SmoothMetric3.squareData F
  have hi : Integrable (fun z : UnitSphere3 ↦ (g.classicalExtension R hR F (r • (z:E3)))^2) angularMeasure :=
    ((continuous_sphere_restriction hr (g.classicalExtension_spec R hR F).1).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun z : UnitSphere3 ↦ g.classicalExtension R hR Q (r • (z:E3))) angularMeasure :=
    (continuous_sphere_restriction hr (g.classicalExtension_spec R hR Q).1).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ sphericalMean (g.classicalExtension R hR Q) r := by
      apply integral_mono hi hj
      intro z
      have hz : ‖(z:E3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using z.property
      have hx : r • (z:E3) ∈ Metric.closedBall (0:E3) R := by
        simpa only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
          abs_of_nonneg hr.1,hz,mul_one] using hr.2
      exact g.ballDirichlet_square R hR F ⟨r • (z:E3),hx⟩
    _ = sphericalMean (Q:E3 → ℝ) R := polar_dirichlet_mean ha hR f H hs hc hb Q hr
    _ = _ := rfl

end HarmonicCounterexample.Main

end

end OAI
