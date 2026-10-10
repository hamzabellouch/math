import OAI.Probability.ContinuumTransition.ConstructionCap

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma physical_kac_locally_uniform {t M a : ℝ} (hcap : ConstructionCap t M) (ha : 0 < a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hm : a+∑' n, σ n ≤ M) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hbound : ∀ n, σ n ≠ 0 → R n ≤ R₀) :
    TendstoLocallyUniformlyOn
      (fun q : ℕ => physicalPressure (physicalProfile t (prepend a σ) (prepend (((q:ℝ)/4)^2) R)) t)
      (meanField (physicalPressure (physicalProfile t σ R) t) a) atTop pressureDomain := by
  have hmass : 0 ≤ ∑' n, σ n := tsum_nonneg hσ
  have hmσ : ∑' n, σ n ≤ M := by linarith only [hm,ha]
  have hma : a ≤ M := by linarith only [hm,hmass]
  have ht := hcap.t_large
  have ht0 := lt_trans zero_lt_one ht
  have hsmall := (strengthened_smallness ht0 (hcap.weak hmσ)).1
  have hgap := strengthened_gap ht0 (hcap.weak hmσ) (hcap.lt_gap hma)
  obtain ⟨C,hC⟩ := exists_lipschitz_kernel
  apply convex_pointwise_locally_uniform isOpen_pressureDomain
  · filter_upwards [eventually_ge_atTop (4:ℕ)] with q hq
    have hr : 1 ≤ ((q:ℝ)/4)^2 := by
      have hh : (4:ℝ) ≤ q := by exact_mod_cast hq
      nlinarith only [hh,sq_nonneg ((q:ℝ)/4-1)]
    apply physical_convex_bounded ht (prepend_nonneg ha.le hσ) (prepend_ge_one hr hR) (summable_prepend a hs)
    rw [tsum_prepend a hs]
    exact hcap.weak hm
  · intro x hx
    rw [meanField_eq (physical_meanField ht ha.le hσ hR hs hsmall hgap.le) hx]
    exact physical_kac_tendsto hC ht hx ha.le hσ hR hs (hcap.small hm) hgap hR₀ hbound x.2

lemma physical_kac_approximate {t M a : ℝ} (hcap : ConstructionCap t M) (ha : 0 < a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hm : a+∑' n, σ n ≤ M) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hbound : ∀ n, σ n ≠ 0 → R n ≤ R₀)
    {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∃ Rnew : ℝ, 4 < Rnew ∧ B < Rnew ∧
      ∀ x ∈ closedBall initialPoint (1/4),
        |physicalPressure (physicalProfile t (prepend a σ) (prepend Rnew R)) t x-
          meanField (physicalPressure (physicalProfile t σ R) t) a x| ≤ ε := by
  have hloc := physical_kac_locally_uniform hcap ha hσ hR hs hm hR₀ hbound
  have hb : closedBall initialPoint (1/4) ⊆ pressureDomain :=
    (closedBall_subset_closedBall (by norm_num : (1:ℝ)/4 ≤ 1/2)).trans (initial_ball_moderate.trans moderateBox_subset)
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_closedBall initialPoint (1/4))).mp (hloc.mono hb)
  have happ := Metric.tendstoUniformlyOn_iff.mp hu ε hε
  have hr : Tendsto (fun q : ℕ => ((q:ℝ)/4)^2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0:ℝ) < 4))
  obtain ⟨q,hq,h4,hB⟩ := (happ.and ((hr.eventually (eventually_gt_atTop (4:ℝ))).and
    (hr.eventually (eventually_gt_atTop B)))).exists
  refine ⟨((q:ℝ)/4)^2,h4,hB,?_⟩
  intro x hx
  simpa only [Real.dist_eq,abs_sub_comm] using (hq x hx).le

end ContinuumTemperature
end
end

end OAI
