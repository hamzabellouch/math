import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.GradientProbes
import OAI.Geometry.WeakHessian.Calculus.CompactSlopeApprox

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile96
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma exists_boundedContinuous_of_compact {f : X → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) : ∃ F : X →ᵇ ℝ,(F : X → ℝ) = f := by
  obtain ⟨R,hR⟩ := (hc.isCompact.image hf).isBounded.subset_closedBall 0
  have hb (x : X) : ‖f x‖ ≤ |R| := by
    by_cases hx : f x = 0
    · simp [hx]
    have H := hR (mem_image_of_mem _ (subset_tsupport _ (Function.mem_support.mpr hx)))
    exact (show ‖f x‖ ≤ R by simpa only [Metric.mem_closedBall,dist_zero_right] using H).trans (le_abs_self _)
  exact ⟨BoundedContinuousFunction.ofNormedAddCommGroup f hf |R| hb,rfl⟩

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integrable_bounded_Lp_sq {v : X → ℝ} (hv : AEStronglyMeasurable v m)
    {B : ℝ} (hvB : ∀ᵐ x ∂m,|v x| ≤ B) (D : Lp ℝ 2 m) :
    Integrable (fun x => v x*(D x)^2) m := by
  apply ((memLp_two_iff_integrable_sq (Lp.memLp D).aestronglyMeasurable).mp (Lp.memLp D)).bdd_mul hv
  simpa only [Real.norm_eq_abs] using hvB

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_bounded_Lp_sq {v : X → ℝ} (hv : AEStronglyMeasurable v m)
    {B : ℝ} (hvB : ∀ᵐ x ∂m,|v x| ≤ B) (D : Lp ℝ 2 m) :
    (∫ x,v x*(D x)^2 ∂m) = ⟪D,boundedMulLp hv hvB D⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMulLp_ae hv hvB D] with x hx
  simp only [RCLike.inner_apply,conj_trivial,hx]
  ring

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma tendsto_integral_bounded_Lp_sq {v : X → ℝ} (hv : AEStronglyMeasurable v m)
    {B : ℝ} (hvB : ∀ᵐ x ∂m,|v x| ≤ B) {Ds : ℕ → Lp ℝ 2 m} {D : Lp ℝ 2 m}
    (hDs : Tendsto Ds atTop (𝓝 D)) :
    Tendsto (fun n => ∫ x,v x*(Ds n x)^2 ∂m) atTop (𝓝 (∫ x,v x*(D x)^2 ∂m)) := by
  simp_rw [integral_bounded_Lp_sq hv hvB]
  exact hDs.inner ((boundedMulLp hv hvB).continuous.continuousAt.tendsto.comp hDs)

lemma RCD.cheegerHeat_weightedEnergy {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D) {t : ℝ} (ht : 0 ≤ t)
    (u : Lp ℝ 2 m) (hu : Integrable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,u x ≤ B) :
    cheegerEnergy (densityMeasure m u) (cheegerHeat h t f : X → ℝ) ≤
      ENNReal.ofReal (Real.exp (-2*K*t)*(∫ x,cheegerHeat h t u x*(D x)^2 ∂m)/2) := by
  obtain ⟨fs,hfl,hfc,hf2,Ds,hDs,hft,hDt⟩ := exists_compact_strong_slope_majorants hfin o hD
    (hrcd.1.global_cheegerEnergy_eq_minimal hfin o hD)
  choose fs' hfs' using fun n => exists_boundedContinuous_of_compact (hfl n).choose_spec.continuous (hfc n)
  have hfl' (n : ℕ) : GloballyLipschitz (fs' n : X → ℝ) := by rw [hfs']; exact hfl n
  have hf2' (n : ℕ) : MemLp (fs' n) 2 m := by rw [hfs']; exact hf2 n
  choose Fs hFl hFe hFb using fun n => hrcd.exists_boundedLipschitz_heatVersion hN hfull hfin h (fs' n) (hfl' n) (hf2' n) ht
  have hn := cheegerHeat_nonneg h ht u hun
  have huabs : ∀ᵐ x ∂m,|u x| ≤ B := by filter_upwards [hun,huB] with x hx hy; rwa [abs_of_nonneg hx]
  have hb := cheegerHeat_bounded h ht hB u huabs
  have hm : densityMeasure m u ≤ ENNReal.ofReal B • m := densityMeasure_le_const huB
  let T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 (densityMeasure m u) := Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top hm
  have hconv : Tendsto (fun n => T (cheegerHeat h t ((hf2 n).toLp (fs n)))) atTop
      (𝓝 (T (cheegerHeat h t f))) :=
    T.continuous.continuousAt.tendsto.comp ((cheegerHeat h t).continuous.continuousAt.tendsto.comp hft)
  have hval := tendsto_integral_bounded_Lp_sq (Lp.memLp (cheegerHeat h t u)).aestronglyMeasurable hb hDt
  have hval' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((hval.const_mul (Real.exp (-2*K*t))).div_const 2)
  have H : cheegerEnergy (densityMeasure m u) (T (cheegerHeat h t f) : X → ℝ) ≤
      ENNReal.ofReal (Real.exp (-2*K*t)*(∫ x,cheegerHeat h t u x*(D x)^2 ∂m)/2) := by
    apply lowerSemicontinuous_cheegerEnergy.isClosed_epigraph.mem_of_tendsto (hconv.prodMk_nhds hval')
    apply Eventually.of_forall
    intro n
    have hfc' : HasCompactSupport (fs' n : X → ℝ) := by rw [hfs']; exact hfc n
    have He := hrcd.cheegerHeat_weightedEnergy_compact hN hfull hfin h o (fs' n) (Fs n)
      (hfl' n) hfc' (hFl n) (hf2' n) ht (hFe n) u hu hun
    have heq : (hf2' n).toLp (fs' n) = (hf2 n).toLp (fs n) := by
      apply Lp.ext
      filter_upwards [(hf2' n).coeFn_toLp,(hf2 n).coeFn_toLp] with x h1 h2
      rw [h1,h2]; exact congrFun (hfs' n) x
    have heq' : (T (cheegerHeat h t ((hf2 n).toLp (fs n))) : X → ℝ) =ᵐ[densityMeasure m u] Fs n := by
      have he := (densityMeasure_ac m u).ae_le (hFe n).symm
      rw [heq] at he
      exact (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top hm _).trans he
    change cheegerEnergy _ _ ≤ _
    rw [cheegerEnergy_congr_ae heq']
    apply He.trans
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply integral_mono_ae (integrable_density_localSlope_sq (cheegerHeat_integrable hfin o h u hu ht).1 (hfl' n).choose_spec)
      (integrable_bounded_Lp_sq (Lp.memLp (cheegerHeat h t u)).aestronglyMeasurable hb (Ds n))
    filter_upwards [hn,hDs n] with x hx hy
    apply mul_le_mul_of_nonneg_left _ hx
    apply sq_le_sq₀ ENNReal.toReal_nonneg hy.1 |>.mpr
    simpa only [hfs' n] using hy.2
  rwa [cheegerEnergy_congr_ae (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top hm _)] at H
end WeakHessian

end
end InlinedFile96

end OAI
