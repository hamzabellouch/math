import OAI.Probability.FreeIsing.Gaussian.TreeEnergy
import OAI.Probability.FreeIsing.Gaussian.TreeResponse

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianTreeResponse

open GaussianTreeCovariance

def finiteRow {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d)) (r : TreeVertex d)
    (h x : TreeVertex d → ℝ) (v : TreeVertex d) (y : E → ℝ) : ℝ :=
  if v ∈ E then response beta E r v
    (fun u => h u + Function.updateFinset x E y u) else 0

lemma integrable_finiteRow_sq {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = [])
    (h x : TreeVertex d → ℝ) (v : TreeVertex d) :
    Integrable (fun y => finiteRow beta E r h x v y ^ 2)
      (Measure.pi (fun u : E => gaussianReal (m u) (t u))) := by
  classical
  by_cases hv : v ∈ E
  · simpa only [finiteRow, ite_eq_left hv] using
      integrable_response_sq hb (P := Measure.pi (fun u : E => gaussianReal (m u) (t u)))
        (X := fun y => Function.updateFinset x E y) (by fun_prop) hE hr
        (fun u _ => by simp [hrnil]) h v hv
  · simp only [finiteRow, ite_eq_right hv, zero_pow (by decide : 2 ≠ 0)]
    exact integrable_zero _ _ _

lemma integral_finiteRow_sq_le {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ u, δ ≤ t u)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = [])
    (h x : TreeVertex d → ℝ) (v : TreeVertex d) :
    (∫ y, finiteRow beta E r h x v y ^ 2
      ∂Measure.pi (fun u : E => gaussianReal (m u) (t u))) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ v.1.length := by
  classical
  by_cases hv : v ∈ E
  · simpa only [finiteRow, ite_eq_left hv, hrnil, List.length_nil, Nat.sub_zero] using
      integral_gaussian_response_sq_le hb m t hδ ht hE hr
        (fun u _ => by simp [hrnil]) h x v hv
  · simp only [finiteRow, ite_eq_right hv, zero_pow (by decide : 2 ≠ 0), integral_zero]
    exact pow_nonneg (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le) _

theorem integral_finiteRow_energy_le {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ u, δ ≤ t u)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = [])
    (h x : TreeVertex d → ℝ) :
    (∫ y, ∑' v, finiteRow beta E r h x v y ^ 2
      ∂Measure.pi (fun u : E => gaussianReal (m u) (t u))) ≤
    1 + (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ) /
      (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ)) := by
  simpa only [one_mul] using integral_tsum_sq_le_of_tree_radial_bound
    (C := 1) (integrable_finiteRow_sq hb m t hE hr hrnil h x)
    (fun v => by simpa only [one_mul] using integral_finiteRow_sq_le hb m t hδ ht hE hr hrnil h x v)
    (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le)
    (gaussian_radial_ratio_lt_one hδ hcrit)

theorem integral_finiteRow_energy_tail_le {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ u, δ ≤ t u)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = [])
    (h x : TreeVertex d → ℝ) (L : ℕ) :
    (∫ y, ∑' v : TreeVertex d, if L < v.1.length then finiteRow beta E r h x v y ^ 2 else 0
      ∂Measure.pi (fun u : E => gaussianReal (m u) (t u))) ≤
    (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ) *
      (((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ)) ^ L /
      (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ)) := by
  simpa only [one_mul] using integral_tsum_sq_cutoff_le_of_tree_radial_bound
    (C := 1) (integrable_finiteRow_sq hb m t hE hr hrnil h x)
    (fun v => by simpa only [one_mul] using integral_finiteRow_sq_le hb m t hδ ht hE hr hrnil h x v)
    (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le)
    (gaussian_radial_ratio_lt_one hδ hcrit) L

end Problem367.GaussianTreeResponse

end

end OAI
