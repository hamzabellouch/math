import Mathlib
import OAI.Analysis.SymmetricDomains.WeightedTaylorUniformlyCompact

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric Asymptotics
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma parabolicScale_tendsto (x : E × F) :
    Tendsto (fun u => parabolicScale u x) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hc : Continuous (fun u => parabolicScale u x) := by
    unfold parabolicScale
    fun_prop
  simpa [parabolicScale,Prod.zero_eq_mk] using (hc.tendsto 0).mono_left
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)

lemma parabolicScale_isBigO (x : E × F) :
    (fun u => parabolicScale u x) =O[𝓝[>] (0:ℝ)] (fun u : ℝ => u) := by
  apply IsBigO.of_bound ‖x‖
  filter_upwards [show ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u from self_mem_nhdsWithin,
    show ∀ᶠ u : ℝ in 𝓝[>] 0, u < 1 from
      (tendsto_order.mp (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0))).2 1 zero_lt_one] with u hu hu1
  simpa only [Real.norm_eq_abs,abs_of_pos hu,mul_comm] using
    parabolicScale_norm hu.le hu1.le x

theorem parabolic_first_derivative {Φ : E × F → G} {L : (E × F) →L[ℝ] G}
    (hΦ : HasFDerivAt Φ L 0) (x : E × F) :
    Tendsto (fun u : ℝ => u⁻¹ • (Φ (parabolicScale u x)-Φ 0))
      (𝓝[>] 0) (𝓝 (L (x.1,0))) := by
  have hrem : (fun u => Φ (parabolicScale u x)-Φ 0-L (parabolicScale u x))
      =o[𝓝[>] (0:ℝ)] (fun u : ℝ => u) := by
    have hh := hΦ.isLittleO.comp_tendsto (parabolicScale_tendsto x)
    simp only [sub_zero,Function.comp_def] at hh
    exact hh.trans_isBigO (parabolicScale_isBigO x)
  have hlin : Tendsto (fun u : ℝ => L (x.1,u • x.2)) (𝓝[>] 0) (𝓝 (L (x.1,0))) := by
    have hc : Continuous (fun u : ℝ => L (x.1,u • x.2)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hsum := hrem.tendsto_inv_smul_nhds_zero.add hlin
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [show ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u from self_mem_nhdsWithin] with u hu
  have hh : parabolicScale u x = u • (x.1,u • x.2) := by
    ext <;> simp [parabolicScale,pow_two,smul_smul]
  rw [hh,map_smul,smul_sub,inv_smul_smul₀ hu.ne',sub_add_cancel]

lemma weighted_first_derivative {Φ : E × F → G} {L : (E × F) →L[ℝ] G}
    (hΦ : HasFDerivAt Φ L 0) (x : E × F) :
    Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹ • (Φ (weightedScale t x)-Φ 0))
      (𝓝[>] 0) (𝓝 (L (x.1,0))) := by
  have hh := (parabolic_first_derivative hΦ x).comp sqrt_tendsto_pos
  apply hh.congr'
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin] with t ht
  simp only [Function.comp_def,parabolicScale,weightedScale,Real.sq_sqrt ht.le]

lemma weighted_squared_chart_limit {Φ : E × F → G} {L : (E × F) →L[ℝ] G}
    (hΦ : HasFDerivAt Φ L 0) (x : E × F) :
    Tendsto (fun t : ℝ => t⁻¹*‖Φ (weightedScale t x)-Φ 0‖^2)
      (𝓝[>] 0) (𝓝 (‖L (x.1,0)‖^2)) := by
  have hh := (weighted_first_derivative hΦ x).norm.pow 2
  apply hh.congr'
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin] with t ht
  simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (Real.sqrt_nonneg t),
    mul_pow,inv_pow,Real.sq_sqrt ht.le]

end Release061

end

end OAI
