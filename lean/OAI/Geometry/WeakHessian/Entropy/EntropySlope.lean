import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.Subdifferential

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile5
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_zero_outside {m : Measure X} {w : X → ℝ} (hw : Measurable w)
    {Q : Set X} (hs : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Q) :
    ∀ᵐ x ∂m, x ∉ Q → w x = 0 := by
  have H := (ae_withDensity_iff (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)).mp hs
  filter_upwards [H] with x hx hnot
  have he : ENNReal.ofReal (w x^2) = 0 := not_not.mp (mt hx hnot)
  have H := ENNReal.ofReal_eq_zero.mp he
  nlinarith [sq_nonneg (w x)]

omit [MetricSpace X] [BorelSpace X] in
lemma integral_mul_le_sqrt_integral_sq {m : Measure X} {f g : X → ℝ}
    (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    (∫ x,f x*g x ∂m) ≤ Real.sqrt (∫ x,f x^2 ∂m)*Real.sqrt (∫ x,g x^2 ∂m) := by
  have he : (∫ x,f x*g x ∂m) = ⟪hf.toLp f,hg.toLp g⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    simp only [hx,hy,RCLike.inner_apply,conj_trivial,mul_comm]
  rw [he,← norm_toLp_sq_eq_integral hf,← norm_toLp_sq_eq_integral hg,
    Real.sqrt_sq (norm_nonneg _),Real.sqrt_sq (norm_nonneg _)]
  exact real_inner_le_norm _ _

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsTestPlan.contact_gamma_fisher_bound (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {w φ ψ : X → ℝ} (hw : Sobolev m w) (hwm : Measurable w) (hwn : ∀ x, 0 ≤ w x)
    {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    (h0 : interpolation π timeZero = squareDensityMeasure m w) :
    (∫ x,2*w x*gamma m φ w x ∂m) ≤
      2*Real.sqrt (∫ x,(weakGradient m w x)^2 ∂m)*Real.sqrt (planEnergy π) := by
  let : IsProbabilityMeasure π := hπ.1
  have hφS := localSobolev_of_lipschitz hfin hφ
  have hφm := (weakGradient_isMinimal hφS.2).1.1.aestronglyMeasurable
  have hwgm := (weakGradient_isMinimal hw.2.1.2).1.1.aestronglyMeasurable
  let f : X → ℝ := fun x => w x*weakGradient m φ x
  have hfm : AEStronglyMeasurable f m := hwm.aestronglyMeasurable.mul hφm
  have hiφ : Integrable (fun x => (weakGradient m φ x)^2) (squareDensityMeasure m w) := by
    rw [← h0]
    exact (integrable_map_measure (hφm.pow 2 |>.mono_ac ((hπ.2.1.choose_spec timeZero).absolutelyContinuous.trans
      (Measure.AbsolutelyContinuous.rfl.smul_left _)))
      (continuous_eval_const timeZero).measurable.aemeasurable).mpr
      (hπ.integrable_gradient_energy hfin hφ timeZero)
  have hf : MemLp f 2 m := by
    apply (memLp_two_iff_integrable_sq hfm).mpr
    convert (squareDensity_integrable hwm).mp hiφ using 1
    funext x
    dsimp [f]
    ring
  have he : (∫ x,f x^2 ∂m) = ∫ γ,(weakGradient m φ (γ timeZero))^2 ∂π := by
    have H := squareDensity_integral (n := m) hwm (fun x => (weakGradient m φ x)^2)
    rw [← h0,interpolation,integral_map (f := fun x => (weakGradient m φ x)^2) (continuous_eval_const timeZero).measurable.aemeasurable
      ((hφm.pow 2).mono_ac ((hπ.2.1.choose_spec timeZero).absolutelyContinuous.trans
        (Measure.AbsolutelyContinuous.rfl.smul_left _)))] at H
    rw [H]
    congr 1
    funext x
    dsimp [f]
    ring
  have hfE : (∫ x,f x^2 ∂m) ≤ planEnergy π := by
    rw [he]
    exact hπ.contact_gradient_energy_le hfin hb hφ hdual hcontact
  have hprod := hf.integrable_mul hw.2.2
  have hΓ : Integrable (fun x => w x*gamma m φ w x) m := by
    apply hprod.mono' (hwm.aestronglyMeasurable.mul (gamma_aestronglyMeasurable hfin hφS hw.2.1))
    filter_upwards [abs_gamma_le hfin hpar hφS hw.2.1] with x hx
    simp only [Pi.mul_apply,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hwn x)]
    dsimp [f]
    nlinarith [mul_le_mul_of_nonneg_left hx (hwn x)]
  have H : (∫ x,w x*gamma m φ w x ∂m) ≤ ∫ x,f x*weakGradient m w x ∂m := by
    apply integral_mono_ae hΓ hprod
    filter_upwards [abs_gamma_le hfin hpar hφS hw.2.1] with x hx
    dsimp [f]
    nlinarith [mul_le_mul_of_nonneg_left ((le_abs_self _).trans hx) (hwn x)]
  have J := integral_mul_le_sqrt_integral_sq hf hw.2.2
  have U := Real.sqrt_le_sqrt hfE
  calc
    _ = 2*(∫ x,w x*gamma m φ w x ∂m) := by rw [← integral_const_mul]; congr 1; funext x; ring
    _ ≤ 2*(Real.sqrt (∫ x,f x^2 ∂m)*Real.sqrt (∫ x,(weakGradient m w x)^2 ∂m)) := by linarith
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right U (Real.sqrt_nonneg (∫ x,(weakGradient m w x)^2 ∂m))]

variable [ProperSpace X]
omit [ProperSpace X] in
lemma squareDensity_sobolev_of_supported (hfin : FiniteOnBoundedSets m)
    {w : X → ℝ} {T : ℝ≥0} (hw : LipschitzWith T w) (o : X) (R : ℝ≥0)
    (hs : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Metric.closedBall o R) : Sobolev m w := by
  apply (localSobolev_of_lipschitz hfin hw).sobolev_of_zero_outside_ball (o := o) (R := (R:ℝ)+1) (by positivity)
  filter_upwards [squareDensity_zero_outside hw.continuous.measurable hs] with x hx hnot
  exact hx (fun h => hnot (by change dist x o < (R:ℝ)+1; exact (show dist x o ≤ R from h).trans_lt (by linarith)))

theorem RCD.bounded_entropy_fisher {m : Measure X} [SigmaFinite m] {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
    (w : X →ᵇ ℝ) {T : ℝ≥0} (hw : LipschitzWith T (w: X → ℝ)) (hwn : ∀ x, 0 ≤ w x)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (o : X) (R : ℝ≥0)
    (hsμ : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hsν : (ν:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCt : C ≠ ∞)
    (hdμ : (μ:Measure X) ≤ C • m) (hdν : (ν:Measure X) ≤ C • m) :
    ∃ π : ProbabilityMeasure (Curve X),
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ ν ∧
      entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+K/2*planEnergy (π:Measure (Curve X)) ≤
        2*Real.sqrt (∫ x,(weakGradient m w x)^2 ∂m)*Real.sqrt (planEnergy (π:Measure (Curve X))) := by
  obtain ⟨π,φ,ψ,hπ,hb,hgeo,hopt,hφ,hψ,hdual,hcontact,hent⟩ :=
    hrcd.bounded_entropy_subdifferential hN hfin w hw hwn μ ν hμ o R hsμ hsν hC0 hCt hdμ hdν
  refine ⟨π,hopt,hent.trans ?_⟩
  apply hπ.contact_gamma_fisher_bound hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2)
    hb (squareDensity_sobolev_of_supported hfin hw o R (by rw [← hμ]; exact ae_iff.mpr hsμ))
    hw.continuous.measurable hwn hφ hdual hcontact (hopt.1.interpolation_endpoints.1.trans hμ)

end WeakHessian

end
end InlinedFile5

end OAI
