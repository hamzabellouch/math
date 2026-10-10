import OAI.Probability.InvariantIsing.Cavity.CavityConditioning

namespace OAI

/-! Bounded-test cutoff removal, including a zero restricted normalizer,
and the good-compression/bad-compression split for the full-system tail. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace InvariantIsing

theorem cavity_conditioning_bound_all {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Set X) (hs : MeasurableSet s)
    (f : X → ℝ) (hf : Integrable f μ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |f x| ≤ M) :
    |(∫ x, f x ∂cond μ s) - ∫ x, f x ∂μ| ≤ 2 * M * (1 - μ.real s) := by
  by_cases hz : μ s = 0
  · rw [cond_eq_zero_of_meas_eq_zero hz, integral_zero_measure, zero_sub, abs_neg]
    have hi := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := M)
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
    have hr : μ.real s = 0 := by simp only [Measure.real, hz, ENNReal.toReal_zero]
    rw [hr]
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      hi.trans (by simpa only [probReal_univ, mul_one] using (show M ≤ 2 * M * (1 - 0) by linarith))
  · exact cavity_conditioning_bound μ s hs
      (ENNReal.toReal_pos hz (measure_ne_top μ s)) f hf M hb

/-- Restricting both replicas changes a bounded test by at most four
times its bound times the discarded one-replica mass. -/
theorem cavity_twoReplica_cutoff_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Set X) (hs : MeasurableSet s)
    (f : (Fin 2 → X) → ℝ) (hf : Integrable f (Measure.pi (fun _ : Fin 2 => μ)))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M) :
    |(∫ x, f x ∂cond (Measure.pi (fun _ : Fin 2 => μ)) (univ.pi (fun _ => s))) -
      ∫ x, f x ∂Measure.pi (fun _ : Fin 2 => μ)| ≤ 4 * M * μ.real sᶜ := by
  have hmass : (Measure.pi (fun _ : Fin 2 => μ)).real (univ.pi (fun _ => s)) =
      (μ.real s) ^ 2 := by
    simp only [Measure.real, Measure.pi_pi, Fin.prod_univ_two, ENNReal.toReal_mul, pow_two]
  have ht := cavity_conditioning_bound_all (Measure.pi (fun _ : Fin 2 => μ))
    (univ.pi (fun _ => s)) (MeasurableSet.univ_pi (fun _ => hs)) f hf hM hb
  rw [hmass] at ht
  rw [measureReal_compl hs, probReal_univ]
  refine ht.trans ?_
  have hp : 0 ≤ μ.real s := measureReal_nonneg
  have hp1 : μ.real s ≤ 1 := measureReal_le_one
  nlinarith [mul_nonneg hM (sq_nonneg (1 - μ.real s))]

/-- On the good compression event it suffices to dominate the special
projection norm by an integrable quantity. No inverse-Gram moment on the
bad event is required. -/
theorem cavity_full_radial_tail {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (good : Set Ω)
    (y : Ω → EuclideanSpace ℝ (Fin d)) (T : Ω → ℝ)
    (hT : Integrable T μ) (hT0 : ∀ ω, 0 ≤ T ω)
    (hy : ∀ ω ∈ good, ‖y ω‖ ^ 2 ≤ T ω)
    {K B : ℝ} (hmean : (∫ ω, T ω ∂μ) ≤ K) (hB : 0 < B) :
    μ.real {ω | B < ‖y ω‖} ≤ μ.real goodᶜ + K / B ^ 2 := by
  have hsub : {ω | B < ‖y ω‖} ⊆ goodᶜ ∪ {ω | B ^ 2 ≤ T ω} := by
    intro ω hω
    by_cases hg : ω ∈ good
    · right
      have hyy := hy ω hg
      have hnorm := norm_nonneg (y ω)
      change B < ‖y ω‖ at hω
      exact ((sq_le_sq₀ hB.le hnorm).mpr hω.le).trans hyy
    · exact Or.inl hg
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hT0) hT (B ^ 2)
  have htail : μ.real {ω | B ^ 2 ≤ T ω} ≤ K / B ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hB)).mpr
    calc
      μ.real {ω | B ^ 2 ≤ T ω} * B ^ 2 ≤ ∫ ω, T ω ∂μ := by
        simpa only [mul_comm] using hm
      _ ≤ K := hmean
  exact (measureReal_mono hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add le_rfl htail))

end InvariantIsing

end

end OAI
