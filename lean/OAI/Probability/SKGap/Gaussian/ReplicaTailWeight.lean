import Mathlib
import OAI.Probability.SKGap.Localization.LogPartitionDeviationProbability

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
namespace SKGapCutoff

noncomputable def replicaTailWeight {n : ℕ} (J : Interaction n) (ε : ℝ) : ℝ :=
  ∑ x : Spin n, ∑ y : Spin n, if ε * n < |replicaOverlap x y| then
    Real.exp (energy J x + energy J y) else 0

noncomputable def replicaTail {n : ℕ} (J : Interaction n) (ε : ℝ) : ℝ :=
  ∑ x : Spin n, ∑ y : Spin n, if ε * n < |replicaOverlap x y| then
    gibbs J x * gibbs J y else 0

lemma replicaTailWeight_nonneg {n : ℕ} (J : Interaction n) (ε : ℝ) :
    0 ≤ replicaTailWeight J ε := by
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  split_ifs <;> positivity

lemma replicaTail_eq_ratio {n : ℕ} (J : Interaction n) (ε : ℝ) :
    replicaTail J ε = replicaTailWeight J ε / partition J ^ 2 := by
  unfold replicaTail replicaTailWeight gibbs
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  split_ifs
  · rw [Real.exp_add]
    ring
  · simp

lemma replicaTail_nonneg {n : ℕ} (J : Interaction n) (ε : ℝ) :
    0 ≤ replicaTail J ε := by
  rw [replicaTail_eq_ratio]
  exact div_nonneg (replicaTailWeight_nonneg J ε) (sq_nonneg _)

lemma replicaTailWeight_le_partition_sq {n : ℕ} (J : Interaction n) (ε : ℝ) :
    replicaTailWeight J ε ≤ partition J ^ 2 := by
  rw [partition_sq_eq_sum]
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  split_ifs
  · exact le_rfl
  · positivity

lemma replicaTail_le_one {n : ℕ} (J : Interaction n) (ε : ℝ) :
    replicaTail J ε ≤ 1 := by
  rw [replicaTail_eq_ratio, div_le_one (sq_pos_of_pos (partition_pos J))]
  exact replicaTailWeight_le_partition_sq J ε

lemma integrable_replicaTailWeight (β ε : ℝ) (n : ℕ) :
    Integrable (fun g => replicaTailWeight (sampledInteraction g) ε) (disorderLaw β n) := by
  apply integrable_finsetSum
  intro x _
  apply integrable_finsetSum
  intro y _
  by_cases h : ε * n < |replicaOverlap x y|
  · simp only [h, ite_true]
    exact integrable_exp_combined_energy β x y
  · simp only [h, ite_false]
    exact integrable_zero _ ℝ _

lemma integral_replicaTailWeight (β ε : ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ g, replicaTailWeight (sampledInteraction g) ε ∂disorderLaw β n) =
      Real.exp (β^2*((n : ℝ)-2)/2) *
        ∑ x : Spin n, ∑ y : Spin n, if ε*n < |replicaOverlap x y| then
          Real.exp (β^2 * replicaOverlap x y ^ 2 / (2*n)) else 0 := by
  have hi (x y : Spin n) : Integrable (fun g =>
      if ε*n < |replicaOverlap x y| then
        Real.exp (energy (sampledInteraction g) x + energy (sampledInteraction g) y)
      else 0) (disorderLaw β n) := by
    split_ifs
    · exact integrable_exp_combined_energy β x y
    · exact integrable_zero _ ℝ _
  unfold replicaTailWeight
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hi x y))]
  simp_rw [integral_finsetSum _ (fun y _ => hi _ y), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  split_ifs
  · rw [integral_exp_combined_energy β hn, Real.exp_add]
  · simp

lemma replicaTailWeight_annealed_identity (β ε : ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ g, replicaTailWeight (sampledInteraction g) ε ∂disorderLaw β n) /
        (∫ g, partition (sampledInteraction g) ∂disorderLaw β n)^2 =
      Real.exp (-β^2/2) *
        (∑ x : Spin n, if ε*n < |magnetization x| then
          Real.exp (β^2 * magnetization x ^ 2 / (2*n)) else 0) / (2 : ℝ)^n := by
  rw [integral_replicaTailWeight β ε hn, integral_partition_sampled β hn]
  simp_rw [sum_replicaOverlap _ (fun z => if ε*n < |z| then Real.exp (β^2*z^2/(2*n)) else 0)]
  simp only [Finset.sum_const, Finset.card_univ, card_spin, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat, mul_pow]
  have he : Real.exp (β^2*((n : ℝ)-2)/2) =
      Real.exp (-β^2/2) * Real.exp (β^2*((n : ℝ)-1)/4)^2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  field_simp

lemma sign_square_tail_le (β q ε : ℝ) (hβq : β^2 < q) (hq : q < 1)
    (hε : 0 < ε) {n : ℕ} (hn : 0 < n) :
    (∑ x : Spin n, if ε*n < |magnetization x| then
        Real.exp (β^2 * magnetization x ^ 2 / (2*n)) else 0) / (2 : ℝ)^n ≤
      Real.exp (-((q-β^2)*ε^2*n/2)) * (Real.sqrt (1-q))⁻¹ := by
  have hq0 : 0 ≤ q := (sq_nonneg β).trans hβq.le
  have hqβ : 0 ≤ q-β^2 := sub_nonneg.mpr hβq.le
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs := sign_square_moment_le (Real.sqrt q) (by rwa [Real.sq_sqrt hq0]) hn
  rw [Real.sq_sqrt hq0] at hs
  have hpoint (x : Spin n) :
      (if ε*n < |magnetization x| then Real.exp (β^2 * magnetization x ^ 2 / (2*n)) else 0) ≤
        Real.exp (-((q-β^2)*ε^2*n/2)) * Real.exp (q * magnetization x ^ 2 / (2*n)) := by
    split_ifs with hx
    · rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hsq : ε^2 * (n : ℝ)^2 ≤ magnetization x ^ 2 := by
        have h := (sq_le_sq₀ (by positivity : 0 ≤ ε*(n : ℝ)) (abs_nonneg _)).mpr hx.le
        simpa only [mul_pow, sq_abs] using h
      have hm := mul_le_mul_of_nonneg_left hsq hqβ
      have hd : (q-β^2)*ε^2*n/2 ≤ (q-β^2) * magnetization x ^ 2 / (2*n) := by
        apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ)*n)).mpr
        nlinarith
      rw [sub_mul q (β^2) (magnetization x^2), sub_div] at hd
      linarith
    · positivity
  calc
    _ ≤ (∑ x : Spin n, Real.exp (-((q-β^2)*ε^2*n/2)) *
        Real.exp (q * magnetization x ^ 2 / (2*n))) / (2 : ℝ)^n :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hpoint x) (by positivity)
    _ = Real.exp (-((q-β^2)*ε^2*n/2)) *
        ((∑ x : Spin n, Real.exp (q * magnetization x^2/(2*n))) / (2 : ℝ)^n) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le

lemma replicaTailWeight_annealed_bound (β q ε : ℝ) (hβq : β^2 < q) (hq : q < 1)
    (hε : 0 < ε) {n : ℕ} (hn : 0 < n) :
    (∫ g, replicaTailWeight (sampledInteraction g) ε ∂disorderLaw β n) /
        (∫ g, partition (sampledInteraction g) ∂disorderLaw β n)^2 ≤
      Real.exp (-((q-β^2)*ε^2*n/2)) * (Real.sqrt (1-q))⁻¹ := by
  rw [replicaTailWeight_annealed_identity β ε hn, mul_div_assoc]
  have he : Real.exp (-β^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg β])
  calc
    _ ≤ Real.exp (-β^2/2) * (Real.exp (-((q-β^2)*ε^2*n/2)) * (Real.sqrt (1-q))⁻¹) :=
      mul_le_mul_of_nonneg_left (sign_square_tail_le β q ε hβq hq hε hn) (Real.exp_pos _).le
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right he (by positivity)

lemma probability_markov_real {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsFiniteMeasure μ] (Y : E → ℝ) (hY : Integrable Y μ) (hY0 : ∀ x, 0 ≤ Y x)
    (t : ℝ) (ht : 0 < t) :
    μ {x | t ≤ Y x} ≤ ENNReal.ofReal ((∫ x, Y x ∂μ) / t) := by
  have h := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Filter.Eventually.of_forall hY0) hY t
  rw [mul_comm t, ← le_div_iff₀ ht] at h
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal h

lemma scalar_log_ratio_tail (Z m W δ a : ℝ) (hZ0 : 0 < Z) (hm : 0 < m)
    (hδ : 0 < δ) (hlog : Real.log m-a ≤ Real.log Z) (hW : δ < W/Z^2) :
    δ * Real.exp (-2*a) ≤ W/m^2 := by
  have hZ : m * Real.exp (-a) ≤ Z := by
    have he := Real.exp_le_exp.mpr hlog
    rw [show Real.log m-a = Real.log m + (-a) by ring, Real.exp_add,
      Real.exp_log hm, Real.exp_log hZ0] at he
    exact he
  have hZ2 := pow_le_pow_left₀ (mul_nonneg hm.le (Real.exp_pos _).le) hZ 2
  have he : (m * Real.exp (-a))^2 = m^2 * Real.exp (-2*a) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [he] at hZ2
  rw [lt_div_iff₀ (sq_pos_of_pos hZ0)] at hW
  apply (le_div_iff₀ (sq_pos_of_pos hm)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hZ2 hδ.le]

lemma divide_exponential_scalar (W m δ a : ℝ) :
    (W/m^2) / (δ*Real.exp (-2*a)) = (Real.exp (2*a)/δ) * (W/m^2) := by
  rw [show -2*a = -(2*a) by ring, Real.exp_neg]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

lemma replicaTail_probability_transfer (β ε δ a : ℝ) {n : ℕ} (hn : 0 < n)
    (hδ : 0 < δ) :
    (disorderLaw β n) {g | δ < replicaTail (sampledInteraction g) ε} ≤
      (disorderLaw β n) {g | Real.log (partition (sampledInteraction g)) <
        Real.log (∫ h, partition (sampledInteraction h) ∂disorderLaw β n) - a} +
      ENNReal.ofReal ((Real.exp (2*a)/δ) *
        ((∫ g, replicaTailWeight (sampledInteraction g) ε ∂disorderLaw β n) /
          (∫ g, partition (sampledInteraction g) ∂disorderLaw β n)^2)) := by
  let μ := disorderLaw β n
  let : IsProbabilityMeasure μ := by dsimp [μ, disorderLaw]; infer_instance
  let m := ∫ g, partition (sampledInteraction g) ∂μ
  have hm : 0 < m := by dsimp [m, μ]; rw [integral_partition_sampled β hn]; positivity
  let Y := fun g : GaussianCoordinates n => replicaTailWeight (sampledInteraction g) ε / m^2
  let t := δ * Real.exp (-2*a)
  have ht : 0 < t := by dsimp [t]; positivity
  have hY : Integrable Y μ := (integrable_replicaTailWeight β ε n).div_const _
  have hY0 (g) : 0 ≤ Y g := div_nonneg (replicaTailWeight_nonneg _ ε) (sq_nonneg _)
  have hsub : {g | δ < replicaTail (sampledInteraction g) ε} ⊆
      {g | Real.log (partition (sampledInteraction g)) < Real.log m - a} ∪ {g | t ≤ Y g} := by
    intro g hg
    by_cases hl : Real.log (partition (sampledInteraction g)) < Real.log m - a
    · exact Or.inl hl
    right
    change δ * Real.exp (-2*a) ≤ replicaTailWeight (sampledInteraction g) ε / m^2
    apply scalar_log_ratio_tail _ _ _ _ _ (partition_pos _) hm hδ (le_of_not_gt hl)
    rwa [← replicaTail_eq_ratio]
  have hmarkov := probability_markov_real μ Y hY hY0 t ht
  have hid : (∫ g, Y g ∂μ) / t = (Real.exp (2*a)/δ) *
      ((∫ g, replicaTailWeight (sampledInteraction g) ε ∂μ) / m^2) := by
    dsimp [Y, t]
    rw [integral_div, divide_exponential_scalar]
  rw [hid] at hmarkov
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl hmarkov))

lemma replicaTail_disorder_probability_bound (β q ε δ : ℝ) (hβq : β^2 < q)
    (hq : q < 1) (hε : 0 < ε) (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) :
    (disorderLaw β n) {g | δ < replicaTail (sampledInteraction g) ε} ≤
      (disorderLaw β n) {g | (q-β^2)*ε^2/8 <
        |(Real.log (partition (sampledInteraction g)) -
          Real.log (∫ h, partition (sampledInteraction h) ∂disorderLaw β n)) / n|} +
      ENNReal.ofReal (((Real.sqrt (1-q))⁻¹ / δ) * Real.exp (-((q-β^2)*ε^2*n/4))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := replicaTail_probability_transfer β ε δ ((q-β^2)*ε^2*n/8) hn hδ
  apply h.trans
  apply add_le_add
  · apply measure_mono
    intro g hg
    have hd : (Real.log (partition (sampledInteraction g)) -
        Real.log (∫ h, partition (sampledInteraction h) ∂disorderLaw β n)) / n <
          -((q-β^2)*ε^2/8) := by
      apply (div_lt_iff₀ hnR).mpr
      change Real.log (partition (sampledInteraction g)) < _ at hg
      linarith
    change (q-β^2)*ε^2/8 < _
    linarith [neg_le_abs ((Real.log (partition (sampledInteraction g)) -
        Real.log (∫ h, partition (sampledInteraction h) ∂disorderLaw β n)) / n)]
  · apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (Real.exp (2*((q-β^2)*ε^2*n/8))/δ) *
          (Real.exp (-((q-β^2)*ε^2*n/2)) * (Real.sqrt (1-q))⁻¹) :=
        mul_le_mul_of_nonneg_left (replicaTailWeight_annealed_bound β q ε hβq hq hε hn)
          (by positivity)
      _ = _ := by
        have he : Real.exp (2*((q-β^2)*ε^2*(n : ℝ)/8)) *
            Real.exp (-((q-β^2)*ε^2*n/2)) = Real.exp (-((q-β^2)*ε^2*n/4)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          _ = (Real.exp (2*((q-β^2)*ε^2*(n : ℝ)/8)) *
            Real.exp (-((q-β^2)*ε^2*n/2))) * (Real.sqrt (1-q))⁻¹ / δ := by ring
          _ = _ := by rw [he]; ring

lemma replica_overlap_vanishes (β : ℝ) (hβ : β^2 < 1) (ε : ℝ) (hε : 0 < ε) :
    DisorderLimit β (fun _ J => replicaTail J ε) 0 := by
  intro δ hδ
  let q := (β^2+1)/2
  have hβq : β^2 < q := by dsimp [q]; linarith
  have hq : q < 1 := by dsimp [q]; linarith
  have ha : 0 < (q-β^2)*ε^2/8 := by positivity
  have hb : 0 < (q-β^2)*ε^2/4 := by positivity
  have hlog := log_partition_annealed_difference_limit β hβ ((q-β^2)*ε^2/8) ha
  simp only [sub_zero] at hlog
  have hexp : Tendsto (fun n : ℕ => Real.exp (-((q-β^2)*ε^2*n/4))) atTop (nhds 0) := by
    have hlin := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
      |>.const_mul_atTop hb
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
    convert he using 1
    ext n
    congr 1
    ring
  have hbound : Tendsto (fun n : ℕ => ENNReal.ofReal (((Real.sqrt (1-q))⁻¹/δ) *
      Real.exp (-((q-β^2)*ε^2*n/4)))) atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hexp.const_mul ((Real.sqrt (1-q))⁻¹/δ))
  have hsum := hlog.add hbound
  simp only [zero_add] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa only [sub_zero, abs_of_nonneg (replicaTail_nonneg _ _)] using
    replicaTail_disorder_probability_bound β q ε δ hβq hq hε hδ (by omega : 0 < n)

end SKGapCutoff

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise

end

end OAI
