import OAI.Probability.FreeIsing.Brownian.PosteriorBareResponse
import OAI.Probability.FreeIsing.Critical.CanonicalResponse
import OAI.Probability.FreeIsing.Gaussian.TreeResponseObservedPosterior

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

open PlantedSymmetry

namespace CriticalCanonicalRowEnergy

def rate (beta : ℝ) (t : ℝ≥0) : ℝ :=
  ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
    min (Real.sqrt (t : ℝ)) 1

theorem rate_pos {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) : 0 < rate beta t := by
  have htheta : 0 < Real.tanh beta := by
    have hn := tanh_nonneg_of_beta_nonneg hb
    by_contra h
    have hz : Real.tanh beta = 0 := le_antisymm (not_lt.mp h) hn
    simp [hz] at hc
  exact mul_pos (ComponentSignalAttenuation.lossCoefficient_pos htheta
    (Real.tanh_lt_one beta))
    (lt_min (Real.sqrt_pos.mpr (show (0 : ℝ) < t from ht)) zero_lt_one)

theorem branching_ratio {d : ℕ} {beta : ℝ}
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) (t : ℝ≥0) :
    ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * Real.exp (-rate beta t)) =
      Real.exp (-rate beta t) := by rw [← mul_assoc, hc, one_mul]

theorem ratio_lt_one {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) :
    ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * Real.exp (-rate beta t)) < 1 := by
  rw [branching_ratio hc]
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (rate_pos hb hc ht))

theorem exp_div_one_sub_exp_le_inv {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) / (1 - Real.exp (-x)) ≤ x⁻¹ := by
  have hq : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hcancel] at he
  apply (div_le_iff₀ (sub_pos.mpr hq)).mpr
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hx).mpr (by nlinarith)

end CriticalCanonicalRowEnergy

open CriticalCanonicalRowEnergy

theorem HasFreeIsingLaw.gaussian_rootResponse_critical_radial_bound
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (v : TreeVertex d) :
    (∫ p, gaussianPosteriorResponse μ t (ConnectedHull.root d) v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh beta ^ 2 * Real.exp (-rate beta t)) ^ v.1.length := by
  have h := hμ.integral_gaussianRootResponse_sq_le_critical hb hd hc ht v
  simpa only [rate, mul_pow, ← pow_mul, Nat.mul_comm,
    ← Real.exp_nat_mul, mul_comm] using h

theorem HasFreeIsingLaw.gaussian_rootResponse_critical_row_energy
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) :
    (∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Summable (fun v => gaussianPosteriorResponse μ t (ConnectedHull.root d) v p ^ 2)) ∧
    Integrable (fun p => ∑' v, gaussianPosteriorResponse μ t (ConnectedHull.root d) v p ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    (∫ p, ∑' v, gaussianPosteriorResponse μ t (ConnectedHull.root d) v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      1 + (d : ℝ) * Real.tanh beta ^ 2 * Real.exp (-rate beta t) /
        (1 - Real.exp (-rate beta t)) := by
  have hold := hμ.gaussian_posteriorResponse_row_energy hb ht hc.le
    (ConnectedHull.root d) rfl
  refine ⟨hold.1, hold.2.1, ?_⟩
  have h := integral_tsum_sq_le_of_tree_radial_bound (C := 1)
    (fun v => (hμ.gaussian_posteriorResponse_sq_decay hb ht (ConnectedHull.root d) v rfl).1)
    (fun v => by simpa only [one_mul] using
      hμ.gaussian_rootResponse_critical_radial_bound hb hd hc ht v)
    (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (ratio_lt_one hb hc ht)
  simpa only [one_mul, branching_ratio hc, mul_assoc] using h

theorem HasFreeIsingLaw.integral_gaussian_rootResponse_row_le_inv_rate
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) :
    (∫ p, ∑' v, gaussianPosteriorResponse μ t (ConnectedHull.root d) v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      1 + (d : ℝ) * Real.tanh beta ^ 2 / rate beta t := by
  apply (hμ.gaussian_rootResponse_critical_row_energy hb hd hc ht).2.2.trans
  have h := mul_le_mul_of_nonneg_left
    (exp_div_one_sub_exp_le_inv (rate_pos hb hc ht))
    (mul_nonneg (Nat.cast_nonneg d) (sq_nonneg (Real.tanh beta)))
  simpa only [mul_div_assoc, div_eq_mul_inv, mul_assoc] using
    add_le_add (show (1 : ℝ) ≤ 1 from le_rfl) h

theorem HasFreeIsingLaw.gaussian_rootResponse_critical_row_tail
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (L : ℕ) :
    (∫ p, ∑' v : TreeVertex d, if L < v.1.length then
      gaussianPosteriorResponse μ t (ConnectedHull.root d) v p ^ 2 else 0
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (d : ℝ) * Real.tanh beta ^ 2 * Real.exp (-rate beta t) *
        Real.exp (-rate beta t) ^ L / (1 - Real.exp (-rate beta t)) := by
  have h := integral_tsum_sq_cutoff_le_of_tree_radial_bound (C := 1)
    (fun v => (hμ.gaussian_posteriorResponse_sq_decay hb ht (ConnectedHull.root d) v rfl).1)
    (fun v => by simpa only [one_mul] using
      hμ.gaussian_rootResponse_critical_radial_bound hb hd hc ht v)
    (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (ratio_lt_one hb hc ht) L
  simpa only [one_mul, branching_ratio hc, mul_assoc] using h

theorem HasFreeIsingLaw.lintegral_gaussian_rootResponse_row_le_inv_rate
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) :
    (∫⁻ p, ∑' v, ENNReal.ofReal
      (gaussianPosteriorResponse μ t (ConnectedHull.root d) v p ^ 2)
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      ENNReal.ofReal (1 + (d : ℝ) * Real.tanh beta ^ 2 / rate beta t) := by
  have hrow := hμ.gaussian_rootResponse_critical_row_energy hb hd hc ht
  have he := hrow.1.mono fun p hp =>
    ENNReal.ofReal_tsum_of_nonneg (fun v => sq_nonneg
      (gaussianPosteriorResponse μ t (ConnectedHull.root d) v p)) hp
  rw [← lintegral_congr_ae he,
    ← ofReal_integral_eq_lintegral_ofReal hrow.2.1
      (Eventually.of_forall fun p => tsum_nonneg (fun v => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal
    (hμ.integral_gaussian_rootResponse_row_le_inv_rate hb hd hc ht)

theorem HasFreeIsingLaw.brownian_rootResponse_critical_row_energy
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hc : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) {t : ℝ≥0} (ht : 0 < t) :
    (∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      Summable (fun v => brownianPosteriorResponse μ ν B t (ConnectedHull.root d) v p ^ 2)) ∧
    Integrable (fun p => ∑' v,
      brownianPosteriorResponse μ ν B t (ConnectedHull.root d) v p ^ 2)
      (μ.prod (Measure.infinitePi ν)) ∧
    (∫ p, ∑' v, brownianPosteriorResponse μ ν B t (ConnectedHull.root d) v p ^ 2
      ∂μ.prod (Measure.infinitePi ν)) ≤
      1 + (d : ℝ) * Real.tanh beta ^ 2 / rate beta t := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hT := (MeasurePreserving.id μ).prod
    (brownian_array_eval_measurePreserving ν hB hmB t)
  have hg := hμ.gaussian_rootResponse_critical_row_energy hb hd hc ht
  have heq := ae_all_iff.mpr (fun v => brownian_past_posteriorResponse_eq_gaussian
    μ ν hB hmB t (ConnectedHull.root d) v)
  have he : (fun p => ∑' v,
      brownianPosteriorResponse μ ν B t (ConnectedHull.root d) v p ^ 2) =ᵐ[
        μ.prod (Measure.infinitePi ν)]
      (fun q => ∑' v, gaussianPosteriorResponse μ t (ConnectedHull.root d) v q ^ 2) ∘
        Prod.map id (fun p i => B i t (p i)) := by
    filter_upwards [heq] with p hp
    exact tsum_congr fun v => congrArg (fun x : ℝ => x ^ 2) (hp v)
  refine ⟨?_, (hT.integrable_comp_of_integrable hg.2.1).congr he.symm, ?_⟩
  · filter_upwards [hT.quasiMeasurePreserving.ae hg.1, heq] with p hp hpeq
    exact hp.congr fun v => congrArg (fun x : ℝ => x ^ 2) (hpeq v).symm
  · rw [integral_congr_ae he, hT.hasLaw.integral_comp hg.2.1.aestronglyMeasurable]
    exact hμ.integral_gaussian_rootResponse_row_le_inv_rate hb hd hc ht

end Problem367

end

end OAI
