import OAI.Probability.FreeIsing.Gaussian.TreeResponseRootPosterior
import OAI.Probability.FreeIsing.Gibbs.CovarianceEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace Problem367
open PlantedSymmetry GaussianTreeCovariance

theorem integral_finiteGibbsCovariance_sq_le_distance {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    {beta : ℝ} (hb : 0 ≤ beta) {t δ : ℝ≥0} (hδ : 0 < δ) (ht : δ ≤ t)
    (v w : TreeVertex d) (n : ℕ) :
    (∫ p, finiteGibbsCovariance beta v w n (observation t p) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ reducedWordDistance v.1 w.1 := by
  apply le_trans (integral_mono
    (integrable_finiteGibbsCovariance_sq beta v w n (measurable_observation t))
    (GaussianTreeResponse.integrable_observedRow_sq_anyroot μ hb t
      (connectedExhaustion_connected v n) ⟨v, mem_connectedExhaustion v n⟩ w)
    (finiteGibbsCovariance_sq_le_observedRow_sq beta v w n t))
  exact GaussianTreeResponse.integral_observedRow_sq_le_distance μ hb hδ ht
    (connectedExhaustion_connected v n) ⟨v, mem_connectedExhaustion v n⟩ w

theorem HasFreeIsingLaw.integral_infiniteGibbsCovariance_sq_le_distance
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t δ : ℝ≥0} (hδ : 0 < δ) (ht : δ ≤ t) (v w : TreeVertex d) :
    (∫ p, infiniteGibbsCovariance beta v w (observation t p) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ reducedWordDistance v.1 w.1 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  exact le_of_tendsto (hμ.finiteGibbsCovariance_tendsto_integral_sq t v w)
    (Eventually.of_forall fun n =>
      integral_finiteGibbsCovariance_sq_le_distance μ hb hδ ht v w n)

theorem summable_geometric_intrinsic {d : ℕ} (v : TreeVertex d) {r : ℝ}
    (hr : 0 ≤ r) (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) :
    Summable (fun w : TreeVertex d => r ^ reducedWordDistance v.1 w.1) := by
  obtain ⟨g, _, hd⟩ := exists_treeAut_to_root_distance v
  apply g.toEquiv.symm.summable_iff.mp
  have hdist (w : TreeVertex d) :
      reducedWordDistance v.1 (g.toEquiv.symm w).1 = w.1.length := by
    simpa only [Equiv.apply_symm_apply] using (hd (g.toEquiv.symm w)).symm
  simpa only [Function.comp_def, hdist] using summable_geometric_radial d hr hsmall

theorem HasFreeIsingLaw.integral_finiteGibbsCovariance_sub_infinite_sq_le_distance
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t δ : ℝ≥0} (hδ : 0 < δ) (ht : δ ≤ t) (v w : TreeVertex d) (n : ℕ) :
    (∫ p, (finiteGibbsCovariance beta v w n (observation t p) -
      infiniteGibbsCovariance beta v w (observation t p)) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      4 * (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ reducedWordDistance v.1 w.1 := by
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
      linarith [integral_finiteGibbsCovariance_sq_le_distance μ hb hδ ht v w n,
        hμ.integral_infiniteGibbsCovariance_sq_le_distance hb hδ ht v w]

theorem HasFreeIsingLaw.finiteGibbsCovariance_tendsto_rowMeanSquare_anyroot
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) :
    Tendsto (fun n => ∑' w, ∫ p,
      (finiteGibbsCovariance beta v w n (observation t p) -
        infiniteGibbsCovariance beta v w (observation t p)) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) atTop (𝓝 0) := by
  have hs := (summable_geometric_intrinsic v
    (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta t).le)
    (gaussian_radial_ratio_lt_one ht hcrit)).mul_left (4 : ℝ)
  have hlim := tendsto_tsum_of_dominated_convergence hs
    (fun w => hμ.finiteGibbsCovariance_tendsto_meanSquare t v w)
    (Eventually.of_forall fun n w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun p => sq_nonneg _))]
      exact hμ.integral_finiteGibbsCovariance_sub_infinite_sq_le_distance
        hb ht le_rfl v w n)
  simpa only [tsum_zero] using hlim

theorem HasFreeIsingLaw.finiteGibbsCovariance_tendsto_integral_rowMeanSquare_anyroot
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) :
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
    exact Summable.of_nonneg_of_le
      (fun w => integral_nonneg (fun p => sq_nonneg _))
      (fun w => hμ.integral_finiteGibbsCovariance_sub_infinite_sq_le_distance
        hb ht le_rfl v w n)
      ((summable_geometric_intrinsic v
        (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta t).le)
        (gaussian_radial_ratio_lt_one ht hcrit)).mul_left 4)
  simp_rw [heq]
  exact hμ.finiteGibbsCovariance_tendsto_rowMeanSquare_anyroot hb ht hcrit v

theorem HasFreeIsingLaw.infiniteGibbsCovariance_row_energy_anyroot
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t δ : ℝ≥0} (hδ : 0 < δ) (ht : δ ≤ t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (r : TreeVertex d) :
    (∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Summable (fun v => infiniteGibbsCovariance beta r v (observation t p) ^ 2)) ∧
    Integrable (fun p => ∑' v, infiniteGibbsCovariance beta r v (observation t p) ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    (∫ p, ∑' v, infiniteGibbsCovariance beta r v (observation t p) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      1 + (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ) /
        (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  obtain ⟨g, _, hd⟩ := exists_treeAut_to_root_distance r
  have hdist (v : TreeVertex d) :
      reducedWordDistance r.1 (g.toEquiv.symm v).1 = v.1.length := by
    simpa only [Equiv.apply_symm_apply] using (hd (g.toEquiv.symm v)).symm
  have hb (v : TreeVertex d) :=
    And.intro
      (integrable_infiniteGibbsCovariance_sq beta r (g.toEquiv.symm v) (measurable_observation t)
        (P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
      (hμ.integral_infiniteGibbsCovariance_sq_le_distance hbeta hδ ht r (g.toEquiv.symm v))
  have hnonneg := mul_nonneg (sq_nonneg (Real.tanh beta)) (gaussianContraction_pos beta δ).le
  have hsmall := gaussian_radial_ratio_lt_one hδ hcrit
  have hbound (v : TreeVertex d) :
      (∫ p, infiniteGibbsCovariance beta r (g.toEquiv.symm v) (observation t p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
        1 * (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ v.1.length := by
    simpa only [hdist, one_mul] using (hb v).2
  have hs' := summable_of_tree_radial_le
    (fun v => integral_nonneg (fun p => sq_nonneg (infiniteGibbsCovariance beta r (g.toEquiv.symm v) (observation t p))))
    hbound hnonneg hsmall
  have hs : Summable (fun v => ∫ p, infiniteGibbsCovariance beta r v (observation t p) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := g.toEquiv.symm.summable_iff.mp hs'
  obtain ⟨hae, hint⟩ := DiscrepancyEnergy.sq_row_integrable_of_summable_integrals
    (fun v => integrable_infiniteGibbsCovariance_sq beta r v (measurable_observation t)) hs
  refine ⟨hae, hint, ?_⟩
  have he := integral_tsum_sq_le_of_tree_radial_bound
    (fun v => (hb v).1) hbound hnonneg hsmall
  have hreindex (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :
      (∑' v, infiniteGibbsCovariance beta r (g.toEquiv.symm v) (observation t p) ^ 2) =
      ∑' v, infiniteGibbsCovariance beta r v (observation t p) ^ 2 :=
    g.toEquiv.symm.tsum_eq (fun v => infiniteGibbsCovariance beta r v (observation t p) ^ 2)
  simpa only [hreindex, one_mul] using he

theorem HasFreeIsingLaw.infiniteGibbsCovariance_row_energy_tail_anyroot
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t δ : ℝ≥0} (hδ : 0 < δ) (ht : δ ≤ t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (r : TreeVertex d) (L : ℕ) :
    (∫ p, ∑' v : TreeVertex d, if L < reducedWordDistance r.1 v.1 then
        infiniteGibbsCovariance beta r v (observation t p) ^ 2 else 0
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ) *
        (((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ)) ^ L /
        (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  obtain ⟨g, _, hd⟩ := exists_treeAut_to_root_distance r
  have hdist (v : TreeVertex d) :
      reducedWordDistance r.1 (g.toEquiv.symm v).1 = v.1.length := by
    simpa only [Equiv.apply_symm_apply] using (hd (g.toEquiv.symm v)).symm
  have hb (v : TreeVertex d) :=
    And.intro
      (integrable_infiniteGibbsCovariance_sq beta r (g.toEquiv.symm v) (measurable_observation t)
        (P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
      (hμ.integral_infiniteGibbsCovariance_sq_le_distance hbeta hδ ht r (g.toEquiv.symm v))
  have hbound (v : TreeVertex d) :
      (∫ p, infiniteGibbsCovariance beta r (g.toEquiv.symm v) (observation t p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
        1 * (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ v.1.length := by
    simpa only [hdist, one_mul] using (hb v).2
  have he := integral_tsum_sq_cutoff_le_of_tree_radial_bound
    (fun v => (hb v).1) hbound
    (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le)
    (gaussian_radial_ratio_lt_one hδ hcrit) L
  have hreindex (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :
      (∑' v : TreeVertex d, if L < reducedWordDistance r.1 v.1 then
        infiniteGibbsCovariance beta r v (observation t p) ^ 2 else 0) =
      ∑' v : TreeVertex d, if L < v.1.length then
        infiniteGibbsCovariance beta r (g.toEquiv.symm v) (observation t p) ^ 2 else 0 := by
    rw [← g.toEquiv.symm.tsum_eq]
    simp only [hdist]
  simp_rw [hreindex]
  simpa only [one_mul] using he

end Problem367

end

end OAI
