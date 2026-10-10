import OAI.Probability.FreeIsing.Gaussian.TreeResponseMixture
import OAI.Probability.FreeIsing.Posterior.PlantedSymmetry

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianTreeResponse

open GaussianTreeCovariance PlantedSymmetry

def spinDrift {d : ℕ} (t : ℝ) (σ : TreeVertex d → IsingSpin) : TreeVertex d → ℝ :=
  fun u => t * spinSign (σ u)

lemma measurable_spinDrift (d : ℕ) (t : ℝ) : Measurable (spinDrift (d := d) t) := by
  exact Measurable.of_eval (fun u =>
    ((measurable_of_finite spinSign).comp (measurable_pi_apply u)).const_mul t)

def observedRow {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d)) (r : TreeVertex d)
    (t : ℝ) (v : TreeVertex d)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) : ℝ :=
  if v ∈ E then response beta E r v (observation t p) else 0

lemma observedRow_eq_shiftedRow {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d))
    (r : TreeVertex d) (t : ℝ) (v : TreeVertex d)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :
    observedRow beta E r t v p =
      shiftedRow beta E r (spinDrift t) (fun _ => 0) v (p.1, E.restrict p.2) := by
  classical
  unfold observedRow shiftedRow finiteRow
  split_ifs with hv
  · apply response_congr
    intro u hu
    simp only [observation, spinDrift, Function.updateFinset, dite_eq_left hu,
      Finset.restrict]
  · rfl

lemma hasLaw_restrict_noise {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (E : Finset (TreeVertex d)) (t : ℝ≥0) :
    HasLaw
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        (p.1, E.restrict p.2))
      (μ.prod (Measure.pi (fun _ : E => gaussianReal 0 t)))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  refine ⟨(measurable_fst.prodMk (E.measurable_restrict.comp measurable_snd)).aemeasurable, ?_⟩
  have hmap := (Measure.map_prod_map μ (gaussianNoiseLaw (TreeVertex d) t)
    measurable_id E.measurable_restrict).symm
  have hfun : Prod.map (id : (TreeVertex d → IsingSpin) → (TreeVertex d → IsingSpin))
      (E.restrict : (TreeVertex d → ℝ) → (E → ℝ)) =
        fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
          (p.1, E.restrict p.2) := by
    funext p
    cases p
    rfl
  rw [hfun] at hmap
  simpa only [gaussianNoiseLaw, Measure.map_id, Measure.infinitePi_map_restrict] using hmap

lemma integrable_observedRow_sq {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    {beta : ℝ} (hb : 0 ≤ beta) (t : ℝ≥0)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = []) (v : TreeVertex d) :
    Integrable (fun p => observedRow beta E r t v p ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  classical
  by_cases hv : v ∈ E
  · simpa only [observedRow, ite_eq_left hv, zero_add] using
      integrable_response_sq hb (P := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (X := observation (t : ℝ)) (measurable_observation t) hE hr
        (fun u _ => by simp [hrnil]) (fun _ => 0) v hv
  · simp only [observedRow, ite_eq_right hv, zero_pow (by decide : 2 ≠ 0)]
    exact integrable_zero _ _ _

theorem integral_observedRow_sq_le {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    {beta : ℝ} (hb : 0 ≤ beta) {t : ℝ≥0} (ht : 0 < t)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = []) (v : TreeVertex d) :
    (∫ p, observedRow beta E r t v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta t) ^ v.1.length := by
  simp_rw [observedRow_eq_shiftedRow]
  have hi := integrable_shiftedRow_sq μ hb (fun _ => 0) (fun _ => t)
    hE hr hrnil (spinDrift t) (measurable_spinDrift d t) (fun _ => 0) v
  have he := (hasLaw_restrict_noise μ E t).integral_comp hi.aestronglyMeasurable
  simp only [Function.comp_apply] at he
  rw [he]
  exact integral_shiftedRow_sq_le μ hb (fun _ => 0) (fun _ => t) ht (fun _ => le_rfl)
    hE hr hrnil (spinDrift t) (measurable_spinDrift d t) (fun _ => 0) v

theorem integral_observedRow_energy_le {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    {beta : ℝ} (hb : 0 ≤ beta) {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = []) :
    (∫ p, ∑' v, observedRow beta E r t v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
    1 + (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t) /
      (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t)) := by
  simpa only [one_mul] using integral_tsum_sq_le_of_tree_radial_bound
    (C := 1) (integrable_observedRow_sq μ hb t hE hr hrnil)
    (fun v => by simpa only [one_mul] using integral_observedRow_sq_le μ hb ht hE hr hrnil v)
    (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta t).le)
    (gaussian_radial_ratio_lt_one ht hcrit)

theorem integral_observedRow_energy_tail_le {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    {beta : ℝ} (hb : 0 ≤ beta) {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = []) (L : ℕ) :
    (∫ p, ∑' v : TreeVertex d,
      if L < v.1.length then observedRow beta E r t v p ^ 2 else 0
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
    (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t) *
      (((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t)) ^ L /
      (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t)) := by
  simpa only [one_mul] using integral_tsum_sq_cutoff_le_of_tree_radial_bound
    (C := 1) (integrable_observedRow_sq μ hb t hE hr hrnil)
    (fun v => by simpa only [one_mul] using integral_observedRow_sq_le μ hb ht hE hr hrnil v)
    (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta t).le)
    (gaussian_radial_ratio_lt_one ht hcrit) L

end Problem367.GaussianTreeResponse

end

end OAI
