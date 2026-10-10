import OAI.Probability.FreeIsing.Gaussian.TreeResponseObservedPosterior
import OAI.Probability.FreeIsing.Gaussian.TreeResponsePlanted
import OAI.Probability.FreeIsing.Gaussian.TreeResponseRootEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianTreeResponse

open GaussianTreeCovariance GaussianTreeResponseNaturality PlantedSymmetry

theorem integrable_shiftedRow_sq_anyroot
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) (u : D)
    (H : Ω → TreeVertex d → ℝ) (hH : Measurable H)
    (x : TreeVertex d → ℝ) (v : TreeVertex d) :
    Integrable (fun p => shiftedRow beta D u H x v p ^ 2)
      (μ.prod (Measure.pi (fun a : D => gaussianReal (m a) (t a)))) := by
  classical
  have hm : Measurable (fun p : Ω × (D → ℝ) => shiftedRow beta D u H x v p ^ 2) := by
    by_cases hv : v ∈ D
    · simp only [shiftedRow, finiteRow, ite_eq_left hv]
      apply Measurable.pow_const
      apply (measurable_response beta D u v).comp
      fun_prop
    · simp only [shiftedRow, finiteRow, ite_eq_right hv, zero_pow (by decide : 2 ≠ 0)]
      exact measurable_const
  apply (integrable_const ((Real.tanh beta ^ reducedWordDistance u.1.1 v.1) ^ 2)).mono'
    hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  have he := pow_le_pow_left₀ (norm_nonneg _) (norm_finiteRow_le_distance hb hD
    (H p.1) x p.2 u v) 2
  simpa only [shiftedRow, Real.norm_eq_abs, abs_pow, sq_abs] using he

theorem integral_shiftedRow_sq_le_distance
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ a, δ ≤ t a)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) (u : D)
    (H : Ω → TreeVertex d → ℝ) (hH : Measurable H)
    (x : TreeVertex d → ℝ) (v : TreeVertex d) :
    (∫ p, shiftedRow beta D u H x v p ^ 2
      ∂μ.prod (Measure.pi (fun a : D => gaussianReal (m a) (t a)))) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^
        reducedWordDistance u.1.1 v.1 := by
  classical
  have hint := integrable_shiftedRow_sq_anyroot μ hb m t hD u H hH x v
  rw [integral_prod _ hint]
  calc
    _ ≤ ∫ _ω, (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^
        reducedWordDistance u.1.1 v.1 ∂μ := by
      apply integral_mono hint.integral_prod_left (integrable_const _)
      intro ω
      by_cases hv : v ∈ D
      · simpa only [shiftedRow, finiteRow, ite_eq_left hv] using
          integral_gaussian_response_sq_le_distance hb m t hδ ht hD (H ω) x u ⟨v, hv⟩
      · simp only [shiftedRow, finiteRow, ite_eq_right hv, zero_pow (by decide : 2 ≠ 0), integral_zero]
        exact pow_nonneg (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le) _
    _ = _ := by simp

theorem integrable_observedRow_sq_anyroot {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    {beta : ℝ} (hb : 0 ≤ beta) (t : ℝ≥0)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) (u : D) (v : TreeVertex d) :
    Integrable (fun p => observedRow beta D u t v p ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  have hi := integrable_shiftedRow_sq_anyroot μ hb (fun _ => 0) (fun _ => t)
    hD u (spinDrift t) (measurable_spinDrift d t) (fun _ => 0) v
  have hp := ((hasLaw_restrict_noise μ D t).measurePreserving
    (measurable_fst.prodMk (D.measurable_restrict.comp measurable_snd))).integrable_comp_of_integrable hi
  simpa only [Function.comp_def, ← observedRow_eq_shiftedRow] using hp

theorem integral_observedRow_sq_le_distance {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    {beta : ℝ} (hb : 0 ≤ beta) {t δ : ℝ≥0} (hδ : 0 < δ) (ht : δ ≤ t)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) (u : D) (v : TreeVertex d) :
    (∫ p, observedRow beta D u t v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^
        reducedWordDistance u.1.1 v.1 := by
  simp_rw [observedRow_eq_shiftedRow]
  have hi := integrable_shiftedRow_sq_anyroot μ hb (fun _ => 0) (fun _ => t)
    hD u (spinDrift t) (measurable_spinDrift d t) (fun _ => 0) v
  have he := (hasLaw_restrict_noise μ D t).integral_comp hi.aestronglyMeasurable
  simp only [Function.comp_apply] at he
  rw [he]
  exact integral_shiftedRow_sq_le_distance μ hb (fun _ => 0) (fun _ => t) hδ (fun _ => ht)
    hD u (spinDrift t) (measurable_spinDrift d t) (fun _ => 0) v

end Problem367.GaussianTreeResponse

namespace Problem367

open Filter PlantedSymmetry GaussianTreeResponse GaussianTreeCovariance
open scoped Topology

theorem HasFreeIsingLaw.finiteObservation_posteriorResponse_sq_bound_distance
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    {t δ : ℝ≥0} (hδ : 0 < δ) (ht : δ ≤ t) (u v : D) :
    let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
    Integrable (fun p => (posteriorResponse P (MeasurableSpace.comap (finiteObservation D t) inferInstance)
      (fun q => spinSign (q.1 u.1)) (fun q => spinSign (q.1 v.1)) p) ^ 2) P ∧
    (∫ p, (posteriorResponse P (MeasurableSpace.comap (finiteObservation D t) inferInstance)
      (fun q => spinSign (q.1 u.1)) (fun q => spinSign (q.1 v.1)) p) ^ 2 ∂P) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^
        reducedWordDistance u.1.1 v.1.1 := by
  dsimp only
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have he := hμ.finiteObservation_posteriorResponse_eq_observedRow D hD t u v
  have he2 := he.fun_comp (fun x : ℝ => x ^ 2)
  simp only [Function.comp_def] at he2
  refine ⟨(integrable_observedRow_sq_anyroot μ hbeta t hD u v.1).congr he2.symm, ?_⟩
  rw [integral_congr_ae he2]
  exact integral_observedRow_sq_le_distance μ hbeta hδ ht hD u v.1

theorem HasFreeIsingLaw.gaussian_posteriorResponse_sq_decay_distance
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t δ : ℝ≥0} (hδ : 0 < δ) (ht : δ ≤ t) (r v : TreeVertex d) :
    Integrable (fun p => gaussianPosteriorResponse μ t r v p ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    (∫ p, gaussianPosteriorResponse μ t r v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ reducedWordDistance r.1 v.1 := by
  obtain ⟨D, hD, hc, hex⟩ := exists_connected_exhaustion r
  apply hμ.gaussian_posteriorResponse_integrable_sq hbeta D hD hex t r v
    (pow_nonneg (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le) _)
  obtain ⟨nr, hnr⟩ := hex r
  obtain ⟨nv, hnv⟩ := hex v
  filter_upwards [eventually_ge_atTop (max nr nv)] with n hn
  have hrn : r ∈ D n := hD (le_trans (le_max_left nr nv) hn) hnr
  have hvn : v ∈ D n := hD (le_trans (le_max_right nr nv) hn) hnv
  exact hμ.finiteObservation_posteriorResponse_sq_bound_distance hbeta (D n) (hc n).1
    hδ ht ⟨r, hrn⟩ ⟨v, hvn⟩

theorem HasFreeIsingLaw.gaussian_posteriorResponse_row_energy_anyroot
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t δ : ℝ≥0} (hδ : 0 < δ) (ht : δ ≤ t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (r : TreeVertex d) :
    (∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Summable (fun v => gaussianPosteriorResponse μ t r v p ^ 2)) ∧
    Integrable (fun p => ∑' v, gaussianPosteriorResponse μ t r v p ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    (∫ p, ∑' v, gaussianPosteriorResponse μ t r v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      1 + (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ) /
        (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ)) := by
  obtain ⟨g, _, hd⟩ := exists_treeAut_to_root_distance r
  have hdist (v : TreeVertex d) :
      reducedWordDistance r.1 (g.toEquiv.symm v).1 = v.1.length := by
    simpa only [Equiv.apply_symm_apply] using (hd (g.toEquiv.symm v)).symm
  have hb (v : TreeVertex d) :=
    hμ.gaussian_posteriorResponse_sq_decay_distance hbeta hδ ht r (g.toEquiv.symm v)
  have hnonneg := mul_nonneg (sq_nonneg (Real.tanh beta)) (gaussianContraction_pos beta δ).le
  have hsmall := gaussian_radial_ratio_lt_one hδ hcrit
  have hbound (v : TreeVertex d) :
      (∫ p, gaussianPosteriorResponse μ t r (g.toEquiv.symm v) p ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
        1 * (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ v.1.length := by
    simpa only [hdist, one_mul] using (hb v).2
  have hs' := summable_of_tree_radial_le
    (fun v => integral_nonneg (fun p => sq_nonneg (gaussianPosteriorResponse μ t r (g.toEquiv.symm v) p)))
    hbound hnonneg hsmall
  have hs : Summable (fun v => ∫ p, gaussianPosteriorResponse μ t r v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := g.toEquiv.symm.summable_iff.mp hs'
  obtain ⟨hae, hint⟩ := DiscrepancyEnergy.sq_row_integrable_of_summable_integrals
    (fun v => (hμ.gaussian_posteriorResponse_sq_decay_distance hbeta hδ ht r v).1) hs
  refine ⟨hae, hint, ?_⟩
  have he := integral_tsum_sq_le_of_tree_radial_bound
    (fun v => (hb v).1) hbound hnonneg hsmall
  have hreindex (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :
      (∑' v, gaussianPosteriorResponse μ t r (g.toEquiv.symm v) p ^ 2) =
      ∑' v, gaussianPosteriorResponse μ t r v p ^ 2 :=
    g.toEquiv.symm.tsum_eq (fun v => gaussianPosteriorResponse μ t r v p ^ 2)
  simpa only [hreindex, one_mul] using he

theorem HasFreeIsingLaw.gaussian_posteriorResponse_row_energy_tail_anyroot
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t δ : ℝ≥0} (hδ : 0 < δ) (ht : δ ≤ t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (r : TreeVertex d) (L : ℕ) :
    (∫ p, ∑' v : TreeVertex d, if L < reducedWordDistance r.1 v.1 then
        gaussianPosteriorResponse μ t r v p ^ 2 else 0
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ) *
        (((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ)) ^ L /
        (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ)) := by
  obtain ⟨g, _, hd⟩ := exists_treeAut_to_root_distance r
  have hdist (v : TreeVertex d) :
      reducedWordDistance r.1 (g.toEquiv.symm v).1 = v.1.length := by
    simpa only [Equiv.apply_symm_apply] using (hd (g.toEquiv.symm v)).symm
  have hb (v : TreeVertex d) :=
    hμ.gaussian_posteriorResponse_sq_decay_distance hbeta hδ ht r (g.toEquiv.symm v)
  have hbound (v : TreeVertex d) :
      (∫ p, gaussianPosteriorResponse μ t r (g.toEquiv.symm v) p ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
        1 * (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ v.1.length := by
    simpa only [hdist, one_mul] using (hb v).2
  have he := integral_tsum_sq_cutoff_le_of_tree_radial_bound
    (fun v => (hb v).1) hbound
    (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le)
    (gaussian_radial_ratio_lt_one hδ hcrit) L
  have hreindex (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :
      (∑' v : TreeVertex d, if L < reducedWordDistance r.1 v.1 then
        gaussianPosteriorResponse μ t r v p ^ 2 else 0) =
      ∑' v : TreeVertex d, if L < v.1.length then
        gaussianPosteriorResponse μ t r (g.toEquiv.symm v) p ^ 2 else 0 := by
    rw [← g.toEquiv.symm.tsum_eq]
    simp only [hdist]
  simp_rw [hreindex]
  simpa only [one_mul] using he

end Problem367

end

end OAI
