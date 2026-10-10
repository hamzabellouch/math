import OAI.Analysis.LipschitzHilbert.Estimates.FiniteVariation
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace OAI

/-! The finite-dimensional Hilbert consequence of the published scalar input. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LipschitzHilbert

theorem measurable_variationCube {Ω : Type*} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n)) (N : ℕ) :
    Measurable (variationCube F N) := by
  classical
  let g := fun (p : Fin (N + 1) → Fin (N + 1)) (x : Ω) =>
    if Monotone p then
      ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ₑ ^ 3 else 0
  have hg (p : Fin (N + 1) → Fin (N + 1)) : Measurable (g p) := by
    by_cases hp : Monotone p
    · simp only [g, ite_eq_left hp]
      exact Finset.measurable_sum _ fun i _ => ((hF _).sub (hF _)).enorm.pow_const _
    · simpa only [g, ite_eq_right hp] using (measurable_const : Measurable (fun _ : Ω => (0 : ℝ≥0∞)))
  have hs (s : Finset (Fin (N + 1) → Fin (N + 1))) :
      Measurable (fun x => s.sup (fun p => g p x)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
      simpa only [Finset.sup_insert] using (hg p).max ih
  exact hs Finset.univ

/-- No extra Hilbert-valued input is assumed: coordinatewise scalar
martingales and finite Minkowski give the same squared Lépingle constant. -/
theorem lepingle_euclidean_bound (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω),
        IsProbabilityMeasure μ → ∀ (κ : Type) [Fintype κ]
          (ℱ : Filtration ℕ m) (F : ℕ → Ω → EuclideanSpace ℝ κ),
          (∀ k, Martingale (fun n x => F n x k) ℱ μ) →
          (∀ k n, MemLp (fun x => F n x k) 2 μ) → ∀ N : ℕ,
            (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) ^
              (2 / 3 : ℝ) ∂μ) ≤
              (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F N x‖ₑ ^ 2 ∂μ := by
  obtain ⟨C, hC, hbound⟩ := hL
  refine ⟨C, hC, ?_⟩
  intro Ω m μ hμ κ inst ℱ F hF hF2 N
  have hmeas (k : κ) (n : ℕ) : Measurable (fun x => F n x k) :=
    ((hF k).stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl
  have hpoint (x : Ω) :
      ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) ^ (2 / 3 : ℝ) ≤
        ∑ k, variationCube (fun n x => F n x k) N x ^ (2 / 3 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num)]
    have h := ENNReal.ofReal_le_ofReal (euclidean_finiteCubicVariation_le (fun n => F n x) N)
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => Real.rpow_nonneg
      (finiteCubicVariation_nonneg _ _) _)] at h
    refine h.trans_eq (Finset.sum_congr rfl fun k _ => ?_)
    rw [← ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _)
      (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    rw [scalar_finiteCubicVariation (fun n x => F n x k) N x]
  calc
    _ ≤ ∫⁻ x, ∑ k, variationCube (fun n x => F n x k) N x ^ (2 / 3 : ℝ) ∂μ :=
      lintegral_mono hpoint
    _ = ∑ k, ∫⁻ x, variationCube (fun n x => F n x k) N x ^ (2 / 3 : ℝ) ∂μ := by
      apply lintegral_finsetSum
      intro k _
      exact (measurable_variationCube _ (hmeas k) N).pow_const _
    _ ≤ ∑ k, (C : ℝ≥0∞) ^ 2 * squareIntegral μ (fun x => F N x k) :=
      Finset.sum_le_sum fun k _ => hbound Ω m μ hμ ℱ _ (hF k) (hF2 k) N
    _ = (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F N x‖ₑ ^ 2 ∂μ := by
      rw [← Finset.mul_sum]
      congr 1
      unfold squareIntegral
      rw [← lintegral_finsetSum]
      · apply lintegral_congr
        intro x
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
          EuclideanSpace.norm_sq_eq, ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
        simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      · intro k _
        exact (hmeas k N).enorm.pow_const _

end LipschitzHilbert

end

end OAI
