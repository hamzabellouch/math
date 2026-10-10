import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.MulBounded
import OAI.Geometry.WeakHessian.Sobolev.LocalSobolevLipschitz

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile26
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X]

def QuadraticLipschitzBound (o : X) (R : ℝ) (f : X → ℝ) : Prop :=
  ∀ x z, |f x-f z| ≤ ((dist x o+dist z o)/2+R)*dist x z

lemma QuadraticLipschitzBound.lipschitzOn_ball {o : X} {R : ℝ} {f : X → ℝ}
    (hf : QuadraticLipschitzBound o R f) (hR : 0 ≤ R) (a : X) (r : ℝ≥0) :
    LipschitzOnWith (NNReal.mk (dist a o+R+r) (by positivity)) f (Metric.closedBall a r) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq]
  apply (hf x y).trans
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  have H := dist_triangle x a o
  have J := dist_triangle y a o
  change dist x a ≤ r at hx
  change dist y a ≤ r at hy
  change (dist x o+dist y o)/2+R ≤ dist a o+R+r
  linarith

lemma QuadraticLipschitzBound.continuous {o : X} {R : ℝ} {f : X → ℝ}
    (hf : QuadraticLipschitzBound o R f) (hR : 0 ≤ R) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (hf.lipschitzOn_ball hR x 1).continuousOn.continuousAt
    (Metric.closedBall_mem_nhds x (by norm_num))

lemma QuadraticLipschitzBound.deriv_comp_bound {o : X} {R : ℝ} {f : X → ℝ}
    (hf : QuadraticLipschitzBound o R f) (hR : 0 < R) (γ : Curve X) (t : ℝ) :
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      ENNReal.ofReal (dist (evalReal γ t) o+R)*metricSpeed γ t := by
  let a := evalReal γ t
  have heps (ε : ℝ) (hε : 0 < ε) :
      ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
        ENNReal.ofReal (dist a o+R+ε)*metricSpeed γ t := by
    obtain ⟨g,hg,heg⟩ := (hf.lipschitzOn_ball hR.le a (NNReal.mk ε hε.le)).extend_real
    have H := deriv_comp_le_metricSpeed_all hg γ t
    have he : (fun s => f (evalReal γ s)) =ᶠ[𝓝 t] (fun s => g (evalReal γ s)) := by
      have ht : Tendsto (evalReal γ) (𝓝 t) (𝓝 a) := (continuous_evalReal.comp (continuous_const.prodMk continuous_id)).continuousAt
      filter_upwards [ht (Metric.closedBall_mem_nhds a hε)] with s hs
      exact heg hs
    rw [← he.deriv_eq] at H
    change ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      (↑(NNReal.mk (dist a o+R+ε) (by positivity)) : ℝ≥0∞)*metricSpeed γ t at H
    rw [← ENNReal.ofReal_eq_coe_nnreal] at H
    exact H
  have hp : ENNReal.ofReal (dist a o+R) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal (dist a o+R+ε)*metricSpeed γ t)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (dist a o+R)*metricSpeed γ t)) := by
    apply ENNReal.Tendsto.mul_const _ (Or.inl hp)
    apply ENNReal.tendsto_ofReal
    simpa only [add_zero,id_eq] using (tendsto_const_nhds (x := dist a o+R)).add (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0))
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ht (eventually_mem_nhdsWithin.mono fun ε hε => heps ε hε)

lemma QuadraticLipschitzBound.comp_ac {o : X} {R : ℝ} {f : X → ℝ}
    (hf : QuadraticLipschitzBound o R f) (hR : 0 ≤ R) {γ : Curve X} (hγ : IsAC2 γ) :
    AbsolutelyContinuousOnInterval (fun s => f (evalReal γ s)) 0 1 := by
  obtain ⟨r,hr,hs⟩ := (isCompact_range γ.continuous).isBounded.subset_closedBall_lt 0 o
  apply ac_comp_lipschitzOn hγ.absolutelyContinuous (hf.lipschitzOn_ball hR o ⟨r,hr.le⟩)
  intro s _hs
  exact hs (mem_range_self (clampTime s))

lemma QuadraticLipschitzBound.endpoint_bound {o : X} {R : ℝ} {f : X → ℝ}
    (hf : QuadraticLipschitzBound o R f) (hR : 0 < R) {γ : Curve X} (hγ : IsAC2 γ) :
    ENNReal.ofReal |f (γ timeOne)-f (γ timeZero)| ≤
      ∫⁻ t in Icc (0:ℝ) 1, ENNReal.ofReal (dist (evalReal γ t) o+R)*metricSpeed γ t := by
  have hac := hf.comp_ac hR.le hγ
  calc
    _ = ‖∫ t in Icc (0:ℝ) 1, deriv (fun s => f (evalReal γ s)) t‖ₑ := by
      rw [← ofReal_norm,Real.norm_eq_abs,integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le zero_le_one,hac.integral_deriv_eq_sub]
      simp [evalReal,clampTime,timeOne,timeZero]
      rfl
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, ‖deriv (fun s => f (evalReal γ s)) t‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ _ := lintegral_mono (fun t => by
      simpa only [← ofReal_norm,Real.norm_eq_abs] using hf.deriv_comp_bound hR γ t)

variable [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma QuadraticLipschitzBound.upperGradient (hfin : FiniteOnBoundedSets m)
    {o : X} {R : ℝ} {f : X → ℝ} (hf : QuadraticLipschitzBound o R f) (hR : 0 < R) :
    IsLocalWeakUpperGradient m f (fun x => dist x o+R) := by
  refine ⟨?_,ae_of_all _ fun x => by positivity,?_⟩
  · intro a r _hr
    let : IsFiniteMeasure (m.restrict (Metric.ball a r)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hfin _ Metric.isBounded_ball⟩
    apply MemLp.of_bound (by fun_prop) (r+dist a o+R)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ dist x o+R)]
    have H := dist_triangle x a o
    change dist x a < r at hx
    linarith
  · intro π hπ _hb
    apply lintegral_mono_ae
    filter_upwards [hπ.2.2.1] with γ hγ
    exact hf.endpoint_bound hR hγ

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

lemma QuadraticLipschitzBound.localSobolev (hfin : FiniteOnBoundedSets m)
    {o : X} {R : ℝ} {f : X → ℝ} (hf : QuadraticLipschitzBound o R f) (hR : 0 < R) :
    LocalSobolev m f := by
  refine ⟨?_,(hf.upperGradient hfin hR).exists_minimal (hf.continuous hR.le).aemeasurable hfin⟩
  intro a r hr
  obtain ⟨g,hg,he⟩ := (hf.lipschitzOn_ball hR.le a ⟨r,hr.le⟩).extend_real
  apply (memLp_congr_ae ?_).mp ((localSobolev_of_lipschitz hfin hg).1 a r hr)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact (he (show dist x a ≤ r from le_of_lt hx)).symm

lemma QuadraticLipschitzBound.gradient_le (hfin : FiniteOnBoundedSets m)
    {o : X} {R : ℝ} {f : X → ℝ} (hf : QuadraticLipschitzBound o R f) (hR : 0 < R) :
    ∀ᵐ x ∂m, weakGradient m f x ≤ dist x o+R :=
  (weakGradient_isMinimal (hf.localSobolev hfin hR).2).2 _ (hf.upperGradient hfin hR)

end WeakHessian

end
end InlinedFile26

end OAI
