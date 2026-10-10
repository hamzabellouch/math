import OAI.Geometry.RCD.Sobolev.LeftDerivativeIntegral
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Passing a uniformly Lipschitz continuity equation to the limit -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem lipschitz_derivative_limit (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ)
    (L : ℝ≥0) {a b A B : ℝ} (hab : a ≤ b)
    (hF : ∀ k, LipschitzOnWith L (F k) (Icc a b))
    (ha : Tendsto (fun k => F k a) atTop (𝓝 A))
    (hb : Tendsto (fun k => F k b) atTop (𝓝 B))
    (hG : ∀ t ∈ Ioo a b, Tendsto (fun k => deriv (F k) t) atTop (𝓝 (G t))) :
    IntervalIntegrable G volume a b ∧ (∫ t in a..b, G t) = B-A := by
  let μ := volume.restrict (Ioc a b)
  have hm k : AEStronglyMeasurable (deriv (F k)) μ := aestronglyMeasurable_deriv (F k) μ
  have hd : ∀ᵐ t ∂μ, Tendsto (fun k => deriv (F k) t) atTop (𝓝 (G t)) := by
    rw [show μ = volume.restrict (Ioo a b) from restrict_Ioo_eq_restrict_Ioc.symm]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hG t ht
  have hbound k : ∀ᵐ t ∂μ, ‖deriv (F k) t‖ ≤ L := by
    rw [show μ = volume.restrict (Ioo a b) from restrict_Ioo_eq_restrict_Ioc.symm]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact norm_deriv_le_of_lipschitzOn (Icc_mem_nhds ht.1 ht.2) (hF k)
  have hGm : AEStronglyMeasurable G μ := aestronglyMeasurable_of_tendsto_ae _ hm hd
  have hGb : ∀ᵐ t ∂μ, ‖G t‖ ≤ L := by
    filter_upwards [hd,ae_all_iff.mpr hbound] with t ht hb
    exact le_of_tendsto ht.norm (Eventually.of_forall hb)
  have hGi : Integrable G μ := (integrable_const (L:ℝ)).mono' hGm hGb
  have hlim := tendsto_integral_of_dominated_convergence (fun _ : ℝ => (L:ℝ)) hm
    (integrable_const (L:ℝ)) hbound hd
  have he k : (∫ t, deriv (F k) t ∂μ) = F k b-F k a := by
    have hFk : LipschitzOnWith L (F k) (uIcc a b) := by simpa only [uIcc_of_le hab] using hF k
    have hh := hFk.absolutelyContinuousOnInterval.integral_deriv_eq_sub
    rwa [intervalIntegral.integral_of_le hab] at hh
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hGi,?_⟩
  rw [intervalIntegral.integral_of_le hab]
  exact tendsto_nhds_unique hlim ((hb.sub ha).congr' (Eventually.of_forall fun k => (he k).symm))

end RegularPointCoordinates

end

end OAI
