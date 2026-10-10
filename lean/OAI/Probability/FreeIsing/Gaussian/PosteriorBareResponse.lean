import OAI.Probability.FreeIsing.Gaussian.TreeResponseObservedPosterior

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

open PlantedSymmetry

theorem HasFreeIsingLaw.finiteObservation_posteriorResponse_mem_Icc
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0) (u v : D) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation D t) inferInstance)
        (fun q => spinSign (q.1 u.1)) (fun q => spinSign (q.1 v.1)) p ∈
        Set.Icc 0 (Real.tanh beta ^ reducedWordDistance u.1.1 v.1.1) := by
  filter_upwards [hμ.finiteObservation_normalizedResponse D hD t u v] with p hp
  change posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (MeasurableSpace.comap (finiteObservation D t) inferInstance)
    (fun q => spinSign (q.1 u.1)) (fun q => spinSign (q.1 v.1)) p = _ at hp
  rw [hp]
  exact TreePathResponse.response_mem_Icc hbeta (observation t p) hD u v

theorem HasFreeIsingLaw.gaussian_posteriorResponse_mem_Icc
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (u v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      gaussianPosteriorResponse μ t u v p ∈
        Set.Icc 0 (Real.tanh beta ^ reducedWordDistance u.1 v.1) := by
  let D := connectedExhaustion u
  have hfin : ∀ n, ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      v ∈ D n → posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation (D n) t) inferInstance)
        (fun q => spinSign (q.1 u)) (fun q => spinSign (q.1 v)) p ∈
        Set.Icc 0 (Real.tanh beta ^ reducedWordDistance u.1 v.1) := by
    intro n
    by_cases hv : v ∈ D n
    · filter_upwards [hμ.finiteObservation_posteriorResponse_mem_Icc hbeta (D n)
        (connectedExhaustion_connected u n) t ⟨u, mem_connectedExhaustion u n⟩
        ⟨v, hv⟩] with p hp
      exact fun _ => hp
    · exact Filter.Eventually.of_forall (fun p hp => False.elim (hv hp))
  have hlim := hμ.gaussian_posteriorResponse_tendsto_ae hbeta D
    (connectedExhaustion_monotone u)
    (fun w => (eventually_mem_connectedExhaustion u w).exists) t u v
  have hall := (ae_all_iff).2 hfin
  filter_upwards [hall, hlim] with p hp hlim
  apply isClosed_Icc.mem_of_tendsto hlim
  filter_upwards [eventually_mem_connectedExhaustion u v] with n hn
  exact hp n hn

theorem HasFreeIsingLaw.gaussian_posteriorResponse_row_bound_of_strict
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (t : ℝ≥0) (u : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Summable (fun v => gaussianPosteriorResponse μ t u v p ^ 2) ∧
      (∑' v, gaussianPosteriorResponse μ t u v p ^ 2) ≤
        1 + (d : ℝ) * Real.tanh beta ^ 2 /
          (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2) ∧
      ∀ L : ℕ, (∑' v : TreeVertex d, if L < reducedWordDistance u.1 v.1
        then gaussianPosteriorResponse μ t u v p ^ 2 else 0) ≤
          (d : ℝ) * Real.tanh beta ^ 2 *
            (((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2) ^ L /
            (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2) := by
  have hall := (ae_all_iff).2 (fun v => hμ.gaussian_posteriorResponse_mem_Icc hbeta t u v)
  obtain ⟨g, _, hd⟩ := exists_treeAut_to_root_distance u
  have hdist (v : TreeVertex d) :
      reducedWordDistance u.1 (g.toEquiv.symm v).1 = v.1.length := by
    simpa only [Equiv.apply_symm_apply] using (hd (g.toEquiv.symm v)).symm
  filter_upwards [hall] with p hp
  have hnorm (v : TreeVertex d) :
      ‖gaussianPosteriorResponse μ t u (g.toEquiv.symm v) p‖ ≤ Real.tanh beta ^ v.1.length := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hp _).1]
    simpa only [hdist] using (hp (g.toEquiv.symm v)).2
  have hs := summable_norm_sq_of_radial_bound d hstrict
    (fun v => gaussianPosteriorResponse μ t u (g.toEquiv.symm v) p) hnorm
  have he := tsum_norm_sq_le_of_radial_bound d hstrict
    (fun v => gaussianPosteriorResponse μ t u (g.toEquiv.symm v) p) hnorm
  simp only [Real.norm_eq_abs, sq_abs] at hs he
  rw [g.toEquiv.symm.tsum_eq (fun v => gaussianPosteriorResponse μ t u v p ^ 2)] at he
  refine ⟨g.toEquiv.symm.summable_iff.mp hs, he, ?_⟩
  intro L
  have hbound (v : TreeVertex d) :
      gaussianPosteriorResponse μ t u (g.toEquiv.symm v) p ^ 2 ≤
        1 * (Real.tanh beta ^ 2) ^ v.1.length := by
    have hv := pow_le_pow_left₀ (norm_nonneg _) (hnorm v) 2
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs, one_mul,
      ← pow_mul, Nat.mul_comm] using hv
  have htail := tsum_cutoff_le_of_tree_radial_le
    (fun v => sq_nonneg (gaussianPosteriorResponse μ t u (g.toEquiv.symm v) p))
    hbound (sq_nonneg _) hstrict L
  rw [← g.toEquiv.symm.tsum_eq (fun v : TreeVertex d =>
    if L < reducedWordDistance u.1 v.1 then gaussianPosteriorResponse μ t u v p ^ 2 else 0)]
  simpa only [hdist, one_mul] using htail

theorem HasFreeIsingLaw.gaussian_posteriorResponse_integrable_energy_of_strict
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (t : ℝ≥0) (u : TreeVertex d) :
    Integrable (fun p => ∑' v, gaussianPosteriorResponse μ t u v p ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    (∫ p, ∑' v, gaussianPosteriorResponse μ t u v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
        1 + (d : ℝ) * Real.tanh beta ^ 2 /
          (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hm (v : TreeVertex d) :
      Measurable (fun p => gaussianPosteriorResponse μ t u v p ^ 2) :=
    (((stronglyMeasurable_posteriorResponse _ _ _ _).mono
      (observationSigma_le (TreeVertex d) t)).measurable).pow_const 2
  have hbound := hμ.gaussian_posteriorResponse_row_bound_of_strict hbeta hstrict t u
  have hint : Integrable (fun p => ∑' v, gaussianPosteriorResponse μ t u v p ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
    apply (integrable_const (1 + (d : ℝ) * Real.tanh beta ^ 2 /
      (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2))).mono'
      (Measurable.tsum hm).aestronglyMeasurable
    filter_upwards [hbound] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => sq_nonneg _))]
    exact hp.2.1
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ _p, (1 + (d : ℝ) * Real.tanh beta ^ 2 /
        (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2))
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t) :=
      integral_mono_ae hint (integrable_const _) (hbound.mono (fun p hp => hp.2.1))
    _ = _ := by simp

end Problem367

end

end OAI
