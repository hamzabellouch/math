import OAI.Probability.FreeIsing.Gaussian.TreeResponseEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianTreeResponse

open GaussianTreeCovariance

def shiftedRow {d : ℕ} {Ω : Type*} (beta : ℝ) (E : Finset (TreeVertex d))
    (r : TreeVertex d) (H : Ω → TreeVertex d → ℝ) (x : TreeVertex d → ℝ)
    (v : TreeVertex d) (p : Ω × (E → ℝ)) : ℝ :=
  finiteRow beta E r (H p.1) x v p.2

lemma integrable_shiftedRow_sq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = [])
    (H : Ω → TreeVertex d → ℝ) (hH : Measurable H)
    (x : TreeVertex d → ℝ) (v : TreeVertex d) :
    Integrable (fun p => shiftedRow beta E r H x v p ^ 2)
      (μ.prod (Measure.pi (fun u : E => gaussianReal (m u) (t u)))) := by
  classical
  by_cases hv : v ∈ E
  · simpa only [shiftedRow, finiteRow, ite_eq_left hv, zero_add] using
      integrable_response_sq hb
        (P := μ.prod (Measure.pi (fun u : E => gaussianReal (m u) (t u))))
        (X := fun p : Ω × (E → ℝ) =>
          fun u => H p.1 u + Function.updateFinset x E p.2 u)
        (by fun_prop) hE hr (fun u _ => by simp [hrnil]) (fun _ => 0) v hv
  · simp only [shiftedRow, finiteRow, ite_eq_right hv, zero_pow (by decide : 2 ≠ 0)]
    exact integrable_zero _ _ _

theorem integral_shiftedRow_sq_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ u, δ ≤ t u)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = [])
    (H : Ω → TreeVertex d → ℝ) (hH : Measurable H)
    (x : TreeVertex d → ℝ) (v : TreeVertex d) :
    (∫ p, shiftedRow beta E r H x v p ^ 2
      ∂μ.prod (Measure.pi (fun u : E => gaussianReal (m u) (t u)))) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ v.1.length := by
  have hint := integrable_shiftedRow_sq μ hb m t hE hr hrnil H hH x v
  rw [integral_prod _ hint]
  calc
    _ ≤ ∫ _ω, (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ v.1.length ∂μ := by
      apply integral_mono hint.integral_prod_left (integrable_const _)
      intro ω
      exact integral_finiteRow_sq_le hb m t hδ ht hE hr hrnil (H ω) x v
    _ = _ := by simp

theorem integral_shiftedRow_energy_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ u, δ ≤ t u)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = [])
    (H : Ω → TreeVertex d → ℝ) (hH : Measurable H) (x : TreeVertex d → ℝ) :
    (∫ p, ∑' v, shiftedRow beta E r H x v p ^ 2
      ∂μ.prod (Measure.pi (fun u : E => gaussianReal (m u) (t u)))) ≤
    1 + (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ) /
      (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ)) := by
  simpa only [one_mul] using integral_tsum_sq_le_of_tree_radial_bound
    (C := 1) (integrable_shiftedRow_sq μ hb m t hE hr hrnil H hH x)
    (fun v => by simpa only [one_mul] using
      integral_shiftedRow_sq_le μ hb m t hδ ht hE hr hrnil H hH x v)
    (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le)
    (gaussian_radial_ratio_lt_one hδ hcrit)

theorem integral_shiftedRow_energy_tail_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ u, δ ≤ t u)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = [])
    (H : Ω → TreeVertex d → ℝ) (hH : Measurable H)
    (x : TreeVertex d → ℝ) (L : ℕ) :
    (∫ p, ∑' v : TreeVertex d,
      if L < v.1.length then shiftedRow beta E r H x v p ^ 2 else 0
      ∂μ.prod (Measure.pi (fun u : E => gaussianReal (m u) (t u)))) ≤
    (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ) *
      (((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ)) ^ L /
      (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ)) := by
  simpa only [one_mul] using integral_tsum_sq_cutoff_le_of_tree_radial_bound
    (C := 1) (integrable_shiftedRow_sq μ hb m t hE hr hrnil H hH x)
    (fun v => by simpa only [one_mul] using
      integral_shiftedRow_sq_le μ hb m t hδ ht hE hr hrnil H hH x v)
    (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le)
    (gaussian_radial_ratio_lt_one hδ hcrit) L

end Problem367.GaussianTreeResponse

end

end OAI
