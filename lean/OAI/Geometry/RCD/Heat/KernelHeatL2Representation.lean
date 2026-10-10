import OAI.Geometry.RCD.Heat.KernelHeatTimeDerivative

namespace OAI

/-! # Kernel representation for every L2 datum

Compact Lipschitz data are dense in L2. The L2 kernel row gives pointwise
convergence, and a subsequence of the actual heat evolutions identifies
the resulting continuous representative.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ) {p : ℝ → X → X → ℝ}
  (hp : IsContinuousHeatKernel μ hQ p)

theorem lp_integrable_dense : Dense {g : Lp ℝ 2 μ | Integrable g μ} := by
  rw [Metric.dense_iff]
  intro f r hr
  obtain ⟨φ,hclose,⟨L,hL⟩,hm,hc⟩ :=
    MemLp.exists_lipschitz_hasCompactSupport_eLpNorm_sub_le μ (Lp.memLp f)
      (ε := ENNReal.ofReal (r/2)) (by positivity)
  refine ⟨hm.toLp φ,?_,(hL.continuous.integrable_of_hasCompactSupport hc).congr hm.coeFn_toLp.symm⟩
  rw [Metric.mem_ball,dist_comm,dist_eq_norm,Lp.norm_def]
  have he : (fun x => (f-hm.toLp φ) x) =ᵐ[μ] (fun x => f x-φ x) := by
    filter_upwards [Lp.coeFn_sub f (hm.toLp φ),hm.coeFn_toLp] with x hx hy
    simp only [hx,Pi.sub_apply,hy]
  rw [eLpNorm_congr_ae he]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hclose).trans_lt
    (by rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ r/2)]; linarith)

theorem kernelHeat_represents_L2 {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ) :
    kernelHeat μ hQ hp t f =ᵐ[μ] heatAt μ hQ t f := by
  obtain ⟨g,hg,hconv⟩ := mem_closure_iff_seq_limit.mp (lp_integrable_dense μ f)
  have hc := ((heatAt μ hQ t).continuous.tendsto f).comp hconv
  obtain ⟨a,ha,hseq⟩ := (tendstoInMeasure_of_tendsto_Lp hc).exists_seq_tendsto_ae
  have he (i : ℕ) := kernelHeat_represents μ hQ hp ht (g i) (hg i)
  filter_upwards [hseq,ae_all_iff.mpr he] with x hx he
  have hk : Tendsto (fun i => kernelHeat μ hQ hp t (g (a i)) x) atTop
      (𝓝 (kernelHeat μ hQ hp t f x)) := by
    exact ((show Continuous (fun g : Lp ℝ 2 μ => inner ℝ (heatKernelRow μ hQ hp t x) g)
      from continuous_const.inner continuous_id).tendsto f).comp (hconv.comp ha.tendsto_atTop)
  apply tendsto_nhds_unique hk
  exact hx.congr' (Eventually.of_forall fun i => (he (a i)).symm)

end RegularPointCoordinates

end

end OAI
