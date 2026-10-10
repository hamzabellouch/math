import OAI.Analysis.LipschitzHilbert.Estimates.VariationIntervals
import OAI.Analysis.LipschitzHilbert.Estimates.HilbertVariation

namespace OAI

/-! Lépingle for disjoint intervals selected separately at each point. -/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace LipschitzHilbert

/-- Freezing a scalar martingale at a deterministic horizon preserves
the original filtration and the terminal value. -/
theorem martingale_freeze {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ} (hF : Martingale F ℱ μ) (N : ℕ) :
    Martingale (fun n => F (min n N)) ℱ μ := by
  constructor
  · intro n
    exact (hF.stronglyMeasurable (min n N)).mono (ℱ.mono (min_le_left n N))
  · intro i j hij
    change μ[F (min j N) | ℱ i] =ᵐ[μ] F (min i N)
    by_cases hi : N ≤ i
    · have hj : N ≤ j := hi.trans hij
      simp only [min_eq_right hi, min_eq_right hj]
      exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (ℱ.le i)
        ((hF.stronglyMeasurable N).mono (ℱ.mono hi)) (hF.integrable N))
    · have hiN : i ≤ N := (lt_of_not_ge hi).le
      rw [min_eq_left hiN]
      exact hF.condExp_ae_eq (le_min hij hiN)

/-- The intervals may depend arbitrarily on the point. A single uniform
published scalar constant controls their Euclidean cubic sum. -/
theorem lepingle_ordered_intervals (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω),
        IsProbabilityMeasure μ → ∀ (κ : Type) [Fintype κ]
          (ℱ : Filtration ℕ m) (F : ℕ → Ω → EuclideanSpace ℝ κ),
          (∀ k, Martingale (fun n x => F n x k) ℱ μ) →
          (∀ k n, MemLp (fun x => F n x k) 2 μ) →
          ∀ (N S : ℕ) (a b : Ω → Fin S → ℕ), S ≤ N →
          (∀ x i, a x i ≤ b x i) → (∀ x i, b x i ≤ N) →
          (∀ x i j, i < j → b x i ≤ a x j) →
            (∫⁻ x, ENNReal.ofReal (∑ i, ‖F (b x i) x - F (a x i) x‖ ^ 3) ^
              (2 / 3 : ℝ) ∂μ) ≤
              (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F N x‖ₑ ^ 2 ∂μ := by
  obtain ⟨C, hC, hbound⟩ := lepingle_euclidean_bound hL
  refine ⟨C, hC, ?_⟩
  intro Ω m μ hμ κ inst ℱ F hF hF2 N S a b hS hab hb horder
  let : IsProbabilityMeasure μ := hμ
  have hmajor := hbound Ω m μ hμ κ ℱ (fun n x => F (min n N) x)
    (fun k => martingale_freeze (hF k) N) (fun k n => hF2 k (min n N)) (2 * N)
  have hterminal : min (2 * N) N = N := min_eq_right (by omega)
  rw [hterminal] at hmajor
  refine (lintegral_mono fun x => ?_).trans hmajor
  exact ENNReal.rpow_le_rpow
    (ENNReal.ofReal_le_ofReal (ordered_intervals_le_variation (fun n => F n x)
      N S (a x) (b x) hS (hab x) (hb x) (horder x))) (by norm_num)

end LipschitzHilbert

end

end OAI
