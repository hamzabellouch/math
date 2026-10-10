import OAI.Analysis.StrictMeans.DyadicBounds

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology

open Set Filter
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

variable {A : Type*} [NormedRing A]

lemma logNormPower_subadditive (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖) :
    Subadditive (fun n => Real.log ‖a ^ n‖) := by
  intro m n
  have hm : 0 < ‖a ^ m‖ := lt_of_lt_of_le zero_lt_one (h m)
  have hn : 0 < ‖a ^ n‖ := lt_of_lt_of_le zero_lt_one (h n)
  calc
    Real.log ‖a ^ (m + n)‖ ≤ Real.log (‖a ^ m‖ * ‖a ^ n‖) :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one (h _)) (by rw [pow_add]; exact norm_mul_le _ _)
    _ = Real.log ‖a ^ m‖ + Real.log ‖a ^ n‖ := Real.log_mul hm.ne' hn.ne'

def logNormGrowth (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖) : ℝ :=
  (logNormPower_subadditive a h).lim

lemma logNormPower_div_bddBelow (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖) :
    BddBelow (range (fun n : ℕ => Real.log ‖a ^ n‖ / n)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact div_nonneg (Real.log_nonneg (h n)) (Nat.cast_nonneg n)

lemma tendsto_logNormGrowth (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖) :
    Tendsto (fun n : ℕ => Real.log ‖a ^ n‖ / n) atTop (𝓝 (logNormGrowth a h)) :=
  (logNormPower_subadditive a h).tendsto_lim (logNormPower_div_bddBelow a h)

lemma logNormGrowth_nonneg (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖) :
    0 ≤ logNormGrowth a h :=
  ge_of_tendsto (tendsto_logNormGrowth a h) (Eventually.of_forall fun n =>
    div_nonneg (Real.log_nonneg (h n)) (Nat.cast_nonneg n))

lemma normPower_eventually_le_exp (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖)
    {b : ℝ} (hb : logNormGrowth a h < b) :
    ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ Real.exp (b * n) := by
  filter_upwards [(tendsto_logNormGrowth a h).eventually (gt_mem_nhds hb),
    eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have he : Real.log ‖a ^ n‖ < b * n := (div_lt_iff₀ hnpos).mp hn
  exact (Real.log_lt_iff_lt_exp (lt_of_lt_of_le zero_lt_one (h n))).mp he |>.le

lemma logNormGrowth_le_of_power_bound (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖)
    {M r : ℝ} (hM : 0 < M) (hr : 0 < r) (hb : ∀ n : ℕ, ‖a ^ n‖ ≤ M * r ^ n) :
    logNormGrowth a h ≤ Real.log r := by
  have hlim : Tendsto (fun n : ℕ => Real.log M / n + Real.log r) atTop (𝓝 (Real.log r)) := by
    simpa using (tendsto_natCast_atTop_atTop.const_div_atTop (Real.log M)).add_const (Real.log r)
  apply le_of_tendsto_of_tendsto (tendsto_logNormGrowth a h) hlim
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hh := Real.log_le_log (lt_of_lt_of_le zero_lt_one (h n)) (hb n)
  rw [Real.log_mul hM.ne' (pow_pos hr n).ne', Real.log_pow] at hh
  rw [div_le_iff₀ hn0]
  calc
    Real.log ‖a ^ n‖ ≤ Real.log M + n * Real.log r := hh
    _ = (Real.log M / n + Real.log r) * n := by field_simp

variable [NormedAlgebra ℝ A] [CompleteSpace A]

lemma summable_resolventPower (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a ^ n‖)
    {τ : ℝ} (hτ : 0 < τ) (hg : logNormGrowth a h < Real.log τ) :
    Summable (fun n : ℕ => (τ⁻¹) ^ n • a ^ n) := by
  obtain ⟨b, hb, hbτ⟩ := exists_between hg
  let r := Real.exp b / τ
  have hr0 : 0 ≤ r := (div_pos (Real.exp_pos b) hτ).le
  have hr1 : r < 1 := by
    apply (div_lt_one hτ).mpr
    exact (Real.exp_lt_exp.mpr hbτ).trans_eq (Real.exp_log hτ)
  have hs : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [normPower_eventually_le_exp a h hb] with n hn
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hτ.le) n)]
  calc
    τ⁻¹ ^ n * ‖a ^ n‖ ≤ τ⁻¹ ^ n * Real.exp (b * n) :=
      mul_le_mul_of_nonneg_left hn (pow_nonneg (inv_nonneg.mpr hτ.le) n)
    _ = r ^ n := by
      rw [mul_comm b (n : ℝ), Real.exp_nat_mul]
      simp [r, div_eq_mul_inv, mul_pow, mul_comm]

end
end StrictInverseFirstPower

end

end OAI
