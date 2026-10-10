import OAI.NumberTheory.JointDickman.Amplification.HalaszMeanLimit

namespace OAI

/-! # Halász mean decay with the manuscript's real cutoff -/
namespace JointDickman
open Complex Finset Filter PublishedInputs
open scoped Topology

lemma primeDistanceSquared_nat_floor (f : ArithmeticFunction ℂ) (X t : ℝ) :
    primeDistanceSquared f (⌊X⌋₊ : ℕ) t = primeDistanceSquared f X t := by
  simp only [primeDistanceSquared, Nat.floor_natCast]

theorem halasz_real_mean_tendsto_zero {ι : Type*} (l : Filter ι)
    (X : ι → ℝ) (hX : Tendsto X l atTop)
    (f : ι → ArithmeticFunction ℂ) (hf : ∀ i, (f i).IsMultiplicative)
    (hnorm : ∀ i n, ‖f i n‖ ≤ 1)
    (hd : Tendsto (fun i => minimumDistance (f i) (X i)) l atTop) :
    Tendsto (fun i => (∑ n ∈ Ioc 0 ⌊X i⌋₊, f i n) / (X i : ℂ)) l (𝓝 0) := by
  have hN := tendsto_nat_floor_atTop.comp hX
  have hmean := halasz_mean_tendsto_zero l (fun i => ⌊X i⌋₊) hN f hf hnorm (by
    intro R
    filter_upwards [hd.eventually_ge_atTop R, hX.eventually_gt_atTop 0] with i hi hXi
    intro t ht
    rw [primeDistanceSquared_nat_floor]
    exact hi.trans (minimumDistance_le_primeDistance (f i) (hnorm i)
      (ht.trans (Nat.floor_le hXi.le))))
  have hnmean := (continuous_norm.tendsto (0 : ℂ)).comp hmean
  simp only [norm_zero] at hnmean
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hnmean.eventually (gt_mem_nhds hε),
    hN.eventually_ge_atTop 1, hX.eventually_gt_atTop 0] with i hi hNi hXi
  have he : Ioc 0 ⌊X i⌋₊ = Icc 1 ⌊X i⌋₊ := by
    ext n
    simp only [mem_Ioc, mem_Icc]
    omega
  rw [dist_eq_norm, sub_zero, he, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hXi]
  simp only [Function.comp_apply] at hi hNi
  rw [norm_div, Complex.norm_natCast] at hi
  have hNi0 : (0 : ℝ) < ⌊X i⌋₊ := by exact_mod_cast (show 0 < ⌊X i⌋₊ by omega)
  exact (div_le_div_of_nonneg_left (norm_nonneg _) hNi0 (Nat.floor_le hXi.le)).trans_lt hi

end JointDickman

end OAI
