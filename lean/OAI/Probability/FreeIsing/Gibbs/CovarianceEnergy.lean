import OAI.Probability.FreeIsing.Gaussian.TreeResponsePlanted
import OAI.Probability.FreeIsing.Gaussian.TreeResponsePosterior
import OAI.Probability.FreeIsing.Gibbs.CovarianceL2Limit

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367

open PlantedSymmetry GaussianTreeCovariance

theorem finiteGibbsCovarianceOn_eq_treeCovariance {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v w : D) (y : TreeVertex d → ℝ) :
    finiteGibbsCovarianceOn beta D v w (D.restrict y) =
      TreePathResponse.covariance beta y D v.1 w.1 := by
  unfold finiteGibbsCovarianceOn TreePathResponse.covariance LeafGibbs.covariance
  simp only [extendFiniteSpin_apply D _ v, extendFiniteSpin_apply D _ w,
    GibbsLeaf.expectation_eq_fieldMean]

theorem TreePathResponse.covariance_sq_le_response_sq {d : ℕ} (beta : ℝ)
    (y : TreeVertex d → ℝ) {D : Finset (TreeVertex d)} {v : TreeVertex d}
    (hv : v ∈ D) (w : TreeVertex d) :
    TreePathResponse.covariance beta y D v w ^ 2 ≤
      TreePathResponse.response beta y D v w ^ 2 := by
  have hp := TreePathResponse.variance_pos beta y hv
  have hle : (1 - TreePathResponse.mean beta y D v ^ 2) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (TreePathResponse.mean beta y D v)]
  rw [TreePathResponse.response, div_pow]
  exact (le_div_iff₀ (sq_pos_of_pos hp)).mpr
    (mul_le_of_le_one_right (sq_nonneg _) hle)

theorem finiteGibbsCovariance_sq_le_observedRow_sq {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) (n : ℕ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :
    finiteGibbsCovariance beta v w n (observation t p) ^ 2 ≤
      GaussianTreeResponse.observedRow beta (connectedExhaustion v n) v t w p ^ 2 := by
  classical
  unfold finiteGibbsCovariance GaussianTreeResponse.observedRow
  split_ifs with hw
  · rw [finiteGibbsCovarianceOn_eq_treeCovariance]
    exact TreePathResponse.covariance_sq_le_response_sq beta _
      (mem_connectedExhaustion v n) w
  · exact le_rfl

lemma integrable_finiteGibbsCovariance_sq {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → TreeVertex d → ℝ} (hX : Measurable X) :
    Integrable (fun ω => finiteGibbsCovariance beta v w n (X ω) ^ 2) P := by
  apply (integrable_const (4 : ℝ)).mono'
    (((continuous_finiteGibbsCovariance beta v w n).measurable.comp hX).pow_const 2).aestronglyMeasurable
  refine Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := finiteGibbsCovariance_abs_le_two beta v w n (X ω)
  have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2 h
  norm_num [sq_abs] at hs
  exact hs

lemma integrable_infiniteGibbsCovariance_sq {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → TreeVertex d → ℝ} (hX : Measurable X) :
    Integrable (fun ω => infiniteGibbsCovariance beta v w (X ω) ^ 2) P := by
  apply (integrable_const (4 : ℝ)).mono'
    (((measurable_infiniteGibbsCovariance beta v w).comp hX).pow_const 2).aestronglyMeasurable
  refine Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := infiniteGibbsCovariance_abs_le_two beta v w (X ω)
  have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2 h
  norm_num [sq_abs] at hs
  exact hs

theorem integral_finiteGibbsCovariance_sq_le {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    {beta : ℝ} (hb : 0 ≤ beta) {t : ℝ≥0} (ht : 0 < t)
    (v w : TreeVertex d) (hv : v.1 = []) (n : ℕ) :
    (∫ p, finiteGibbsCovariance beta v w n (observation t p) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta t) ^ w.1.length := by
  apply le_trans (integral_mono
    (integrable_finiteGibbsCovariance_sq beta v w n (measurable_observation t))
    (GaussianTreeResponse.integrable_observedRow_sq μ hb t
      (connectedExhaustion_connected v n) (mem_connectedExhaustion v n) hv w)
    (finiteGibbsCovariance_sq_le_observedRow_sq beta v w n t))
  exact GaussianTreeResponse.integral_observedRow_sq_le μ hb ht
    (connectedExhaustion_connected v n) (mem_connectedExhaustion v n) hv w

theorem HasFreeIsingLaw.finiteGibbsCovariance_tendsto_integral_sq
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    Tendsto (fun n => ∫ p,
      finiteGibbsCovariance beta v w n (observation t p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) atTop
      (𝓝 (∫ p, infiniteGibbsCovariance beta v w (observation t p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply tendsto_integral_of_dominated_convergence (fun _ => (4 : ℝ))
    (fun n => (((continuous_finiteGibbsCovariance beta v w n).measurable.comp
      (measurable_observation t)).pow_const 2).aestronglyMeasurable)
    (integrable_const _)
  · intro n
    refine Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := finiteGibbsCovariance_abs_le_two beta v w n (observation t p)
    have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2 h
    norm_num [sq_abs] at hs
    exact hs
  · exact (hμ.finiteGibbsCovariance_tendsto_ae t v w).mono fun p hp => hp.pow 2

theorem HasFreeIsingLaw.integral_infiniteGibbsCovariance_sq_le
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t) (v w : TreeVertex d) (hv : v.1 = []) :
    (∫ p, infiniteGibbsCovariance beta v w (observation t p) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta t) ^ w.1.length := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  exact le_of_tendsto (hμ.finiteGibbsCovariance_tendsto_integral_sq t v w)
    (Eventually.of_forall fun n => integral_finiteGibbsCovariance_sq_le μ hb ht v w hv n)

theorem HasFreeIsingLaw.ae_summable_infiniteGibbsCovariance_sq
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (hv : v.1 = []) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Summable (fun w => infiniteGibbsCovariance beta v w (observation t p) ^ 2) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply ae_summable_sq_of_tree_radial_bound (C := 1)
    (fun w => integrable_infiniteGibbsCovariance_sq beta v w (measurable_observation t))
    (fun w => by simpa only [one_mul] using
      hμ.integral_infiniteGibbsCovariance_sq_le hb ht v w hv)
    (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta t).le)
    (gaussian_radial_ratio_lt_one ht hcrit)

theorem HasFreeIsingLaw.integral_infiniteGibbsCovariance_energy_le
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (hv : v.1 = []) :
    (∫ p, ∑' w, infiniteGibbsCovariance beta v w (observation t p) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      1 + (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t) /
        (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  simpa only [one_mul] using integral_tsum_sq_le_of_tree_radial_bound (C := 1)
    (fun w => integrable_infiniteGibbsCovariance_sq beta v w (measurable_observation t))
    (fun w => by simpa only [one_mul] using
      hμ.integral_infiniteGibbsCovariance_sq_le hb ht v w hv)
    (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta t).le)
    (gaussian_radial_ratio_lt_one ht hcrit)

theorem HasFreeIsingLaw.integral_infiniteGibbsCovariance_energy_tail_le
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (hv : v.1 = []) (L : ℕ) :
    (∫ p, ∑' w : TreeVertex d,
      if L < w.1.length then infiniteGibbsCovariance beta v w (observation t p) ^ 2 else 0
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t) *
        (((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t)) ^ L /
        (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  simpa only [one_mul] using integral_tsum_sq_cutoff_le_of_tree_radial_bound (C := 1)
    (fun w => integrable_infiniteGibbsCovariance_sq beta v w (measurable_observation t))
    (fun w => by simpa only [one_mul] using
      hμ.integral_infiniteGibbsCovariance_sq_le hb ht v w hv)
    (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta t).le)
    (gaussian_radial_ratio_lt_one ht hcrit) L

lemma integrable_finiteGibbsCovariance_sub_infinite_sq {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → TreeVertex d → ℝ} (hX : Measurable X) :
    Integrable (fun ω => (finiteGibbsCovariance beta v w n (X ω) -
      infiniteGibbsCovariance beta v w (X ω)) ^ 2) P := by
  have hf := (memLp_two_iff_integrable_sq
    (((continuous_finiteGibbsCovariance beta v w n).measurable.comp hX).aestronglyMeasurable)).2
      (integrable_finiteGibbsCovariance_sq beta v w n (P := P) hX)
  have hi := (memLp_two_iff_integrable_sq
    (((measurable_infiniteGibbsCovariance beta v w).comp hX).aestronglyMeasurable)).2
      (integrable_infiniteGibbsCovariance_sq beta v w (P := P) hX)
  exact (hf.sub hi).integrable_sq

theorem HasFreeIsingLaw.integral_finiteGibbsCovariance_sub_infinite_sq_le
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t) (v w : TreeVertex d) (hv : v.1 = []) (n : ℕ) :
    (∫ p, (finiteGibbsCovariance beta v w n (observation t p) -
      infiniteGibbsCovariance beta v w (observation t p)) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      4 * (Real.tanh beta ^ 2 * gaussianContraction beta t) ^ w.1.length := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hf := integrable_finiteGibbsCovariance_sq beta v w n (measurable_observation t)
    (P := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
  have hi := integrable_infiniteGibbsCovariance_sq beta v w (measurable_observation t)
    (P := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
  calc
    _ ≤ ∫ p, (2 * finiteGibbsCovariance beta v w n (observation t p) ^ 2 +
        2 * infiniteGibbsCovariance beta v w (observation t p) ^ 2)
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t) := by
      apply integral_mono
        (integrable_finiteGibbsCovariance_sub_infinite_sq beta v w n (measurable_observation t))
        ((hf.const_mul 2).add (hi.const_mul 2))
      intro p
      change (finiteGibbsCovariance beta v w n (observation t p) -
        infiniteGibbsCovariance beta v w (observation t p)) ^ 2 ≤
        2 * finiteGibbsCovariance beta v w n (observation t p) ^ 2 +
        2 * infiniteGibbsCovariance beta v w (observation t p) ^ 2
      nlinarith [sq_nonneg (finiteGibbsCovariance beta v w n (observation t p) +
        infiniteGibbsCovariance beta v w (observation t p))]
    _ = 2 * (∫ p, finiteGibbsCovariance beta v w n (observation t p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) +
        2 * (∫ p, infiniteGibbsCovariance beta v w (observation t p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
      rw [integral_add (hf.const_mul 2) (hi.const_mul 2), integral_const_mul, integral_const_mul]
    _ ≤ _ := by
      linarith [integral_finiteGibbsCovariance_sq_le μ hb ht v w hv n,
        hμ.integral_infiniteGibbsCovariance_sq_le hb ht v w hv]

theorem HasFreeIsingLaw.finiteGibbsCovariance_tendsto_rowMeanSquare
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (hv : v.1 = []) :
    Tendsto (fun n => ∑' w, ∫ p,
      (finiteGibbsCovariance beta v w n (observation t p) -
        infiniteGibbsCovariance beta v w (observation t p)) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) atTop (𝓝 0) := by
  have hs := (summable_geometric_radial d
    (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta t).le)
    (gaussian_radial_ratio_lt_one ht hcrit)).mul_left (4 : ℝ)
  have hlim := tendsto_tsum_of_dominated_convergence hs
    (fun w => hμ.finiteGibbsCovariance_tendsto_meanSquare t v w)
    (Eventually.of_forall fun n w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun p => sq_nonneg _))]
      exact hμ.integral_finiteGibbsCovariance_sub_infinite_sq_le hb ht v w hv n)
  simpa only [tsum_zero] using hlim

theorem HasFreeIsingLaw.finiteGibbsCovariance_tendsto_integral_rowMeanSquare
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (hv : v.1 = []) :
    Tendsto (fun n => ∫ p, ∑' w,
      (finiteGibbsCovariance beta v w n (observation t p) -
        infiniteGibbsCovariance beta v w (observation t p)) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have heq (n : ℕ) :
      (∫ p, ∑' w, (finiteGibbsCovariance beta v w n (observation t p) -
        infiniteGibbsCovariance beta v w (observation t p)) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) =
      ∑' w, ∫ p, (finiteGibbsCovariance beta v w n (observation t p) -
        infiniteGibbsCovariance beta v w (observation t p)) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t) := by
    apply (integral_tsum_of_summable_integral_norm
      (fun w => integrable_finiteGibbsCovariance_sub_infinite_sq
        beta v w n (measurable_observation t)) _).symm
    simp only [Real.norm_eq_abs, abs_pow, sq_abs]
    exact summable_of_tree_radial_le
      (fun w => integral_nonneg (fun p => sq_nonneg _))
      (fun w => hμ.integral_finiteGibbsCovariance_sub_infinite_sq_le hb ht v w hv n)
      (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta t).le)
      (gaussian_radial_ratio_lt_one ht hcrit)
  simp_rw [heq]
  exact hμ.finiteGibbsCovariance_tendsto_rowMeanSquare hb ht hcrit v hv

end Problem367

end

end OAI
