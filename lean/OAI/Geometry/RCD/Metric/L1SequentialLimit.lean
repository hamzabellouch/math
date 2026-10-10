import OAI.Geometry.RCD.Metric.MetricSequentialCauchy
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! # An actual L1 limit from pairwise integral convergence -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem exists_L1_limit_of_pairwise {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : ℕ → X → ℝ) (hF : ∀ k, Integrable (F k) μ)
    (hpair : ∀ i j : ℕ → ℕ, Tendsto i atTop atTop → Tendsto j atTop atTop →
      Tendsto (fun k => ∫ x, |F (i k) x-F (j k) x| ∂μ) atTop (𝓝 0)) :
    ∃ H : Lp ℝ 1 μ, Tendsto (fun k => ∫ x, |F k x-H x| ∂μ) atTop (𝓝 0) := by
  let G k := (hF k).toL1 (F k)
  have hdist (i j : ℕ) : dist (G i) (G j) = ∫ x, |F i x-F j x| ∂μ := by
    rw [L1.dist_eq_integral_dist]
    apply integral_congr_ae
    filter_upwards [(hF i).coeFn_toL1,(hF j).coeFn_toL1] with x hi hj
    rw [hi,hj,Real.dist_eq]
  have hc : CauchySeq G := cauchySeq_of_pairwise_tendsto G (by
    intro i j hi hj
    simpa only [hdist] using hpair i j hi hj)
  obtain ⟨H,hH⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨H,?_⟩
  have he (k : ℕ) : dist (G k) H = ∫ x, |F k x-H x| ∂μ := by
    rw [L1.dist_eq_integral_dist]
    apply integral_congr_ae
    filter_upwards [(hF k).coeFn_toL1] with x hx
    rw [hx,Real.dist_eq]
  have hh : Tendsto (fun k => dist (G k) H) atTop (𝓝 (dist H H)) :=
    hH.dist tendsto_const_nhds
  simpa only [he,dist_self] using hh

end RegularPointCoordinates

end

end OAI
