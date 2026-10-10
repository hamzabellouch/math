import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped ENNReal

def innerDyadicAnnulus {d : ℕ} (x : Ambient d) (r : ℝ) (k : ℕ) : Set (Ambient d) :=
  {y | r * (1 / 2 : ℝ) ^ (k + 1) < dist x y ∧ dist x y ≤ r * (1 / 2 : ℝ) ^ k}

theorem innerDyadicAnnulus_measurable {d : ℕ} (x : Ambient d) (r : ℝ) (k : ℕ) :
    MeasurableSet (innerDyadicAnnulus x r k) := by
  exact (measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable).inter
    (measurableSet_le (continuous_const.dist continuous_id).measurable measurable_const)

theorem innerDyadicAnnulus_disjoint {d : ℕ} (x : Ambient d) (r : ℝ) (hr : 0 < r) :
    Pairwise (Disjoint on innerDyadicAnnulus x r) := by
  have hsep {k l : ℕ} (hkl : k < l) : Disjoint (innerDyadicAnnulus x r k)
      (innerDyadicAnnulus x r l) := by
    apply Set.disjoint_left.mpr
    intro y hyk hyl
    have hp : (1 / 2 : ℝ) ^ l ≤ (1 / 2 : ℝ) ^ (k + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.succ_le_of_lt hkl)
    have hm := mul_le_mul_of_nonneg_left hp hr.le
    exact (not_lt_of_ge (hyl.2.trans hm)) hyk.1
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact hsep h
  · exact (hsep h).symm

theorem iUnion_innerDyadicAnnulus {d : ℕ} (x : Ambient d) (r : ℝ) (hr : 0 < r) :
    (⋃ k : ℕ, innerDyadicAnnulus x r k) = closedBall x r \ {x} := by
  ext y
  constructor
  · intro hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    have hp : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hd : 0 < dist x y := lt_trans (by positivity) hk.1
    refine ⟨?_, ?_⟩
    · have h := hk.2.trans (mul_le_mul_of_nonneg_left hp hr.le)
      simpa only [mem_closedBall, dist_comm, mul_one] using! h
    · simpa only [mem_singleton_iff, ne_eq, eq_comm] using! (dist_pos.mp hd)
  · intro hy
    have hd : 0 < dist x y := dist_pos.mpr (by
      simpa only [mem_singleton_iff, ne_eq, eq_comm] using! hy.2)
    have hdist : dist x y ≤ r := by simpa only [mem_closedBall, dist_comm] using! hy.1
    have hratio : dist x y / r ≤ 1 := (div_le_iff₀ hr).mpr (by simpa using! hdist)
    obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near_of_lt_one (div_pos hd hr) hratio
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    refine mem_iUnion.mpr ⟨k, ?_, ?_⟩
    · simpa only [mul_comm] using! (lt_div_iff₀ hr).mp hk₁
    · simpa only [mul_comm] using! (div_le_iff₀ hr).mp hk₂

theorem innerDyadicAnnulus_subset_ball {d : ℕ} (x : Ambient d) (r : ℝ)
    (hr : 0 < r) (k : ℕ) :
    innerDyadicAnnulus x r k ⊆ ball x (2 * (r * (1 / 2 : ℝ) ^ k)) := by
  intro y hy
  have hp : 0 < r * (1 / 2 : ℝ) ^ k := by positivity
  have ht : dist x y < 2 * (r * (1 / 2 : ℝ) ^ k) := by linarith [hy.2]
  simpa only [mem_ball, dist_comm] using! ht

theorem inverseDistancePow_bound_on_innerAnnulus {d : ℕ} (p : ℕ)
    (x : Ambient d) (r : ℝ) (hr : 0 < r) (k : ℕ)
    (y : Ambient d) (hy : y ∈ innerDyadicAnnulus x r k) :
    ‖inverseDistancePow p x y‖ ≤ ((r * (1 / 2 : ℝ) ^ (k + 1)) ^ p)⁻¹ := by
  rw [Real.norm_of_nonneg (inverseDistancePow_nonneg p x y)]
  simpa only [inverseDistancePow, one_div] using!
    one_div_le_one_div_of_le (pow_pos (show 0 < r * (1 / 2 : ℝ) ^ (k + 1) by positivity) p)
      (pow_le_pow_left₀ (by positivity) hy.1.le p)

theorem inverseDistancePow_integrableOn_innerAnnulus {d : ℕ} (n p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (r : ℝ) (hr : 0 < r) (k : ℕ) :
    IntegrableOn (inverseDistancePow p x) (innerDyadicAnnulus x r k) μ := by
  have hfinite : μ (innerDyadicAnnulus x r k) < ∞ :=
    ((measure_mono (innerDyadicAnnulus_subset_ball x r hr k)).trans
      (hg.2 x _ (by positivity))).trans_lt ENNReal.ofReal_lt_top
  apply Measure.integrableOn_of_bounded hfinite.ne
    (inverseDistancePow_measurable p x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (innerDyadicAnnulus_measurable x r k)] with y hy
  exact inverseDistancePow_bound_on_innerAnnulus p x r hr k y hy

theorem singleton_null_of_globalGrowth {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ) (x : Ambient d) :
    μ {x} = 0 := by
  have hh : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (C * ((1 / 2 : ℝ) ^ k) ^ (p + 1)))
      atTop (𝓝 0) := by
    simpa using! ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hh.pow (p + 1)).const_mul C)
  apply le_antisymm _ (zero_le)
  apply ge_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro k
  apply (measure_mono _).trans (hg.2 x _ (by positivity))
  intro y hy
  have hyx : y = x := mem_singleton_iff.mp hy
  subst y
  simpa only [mem_ball, dist_self] using! (show (0 : ℝ) < (1 / 2 : ℝ) ^ k by positivity)

end

end RieszRectifiability

end OAI
