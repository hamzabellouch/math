import OAI.Probability.InvariantIsing.Magnetic.RestrictedCoordinateOverlap

namespace OAI

/-! Averaging the physical coordinate identities yields the exact block test. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma restricted_block_test_eq_average {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (q : OverlapPath) (Φ : ℝ →ᵇ ℝ) :
    (∫ t, Φ (q t) * restrictedBlockOverlapPath hN S hS h t ∂pathMeasure) =
      (N : ℝ)⁻¹ * ∑ j, ∫ t,
        Φ (q t) * restrictedCoordinateOverlapPath hN S hS h j t ∂pathMeasure := by
  have hi (j : Fin N) : Integrable
      (fun t => Φ (q t) * restrictedCoordinateOverlapPath hN S hS h j t) pathMeasure := by
    let p := restrictedCoordinateOverlapPath hN S hS h j
    apply integrable_of_measurable_abs_le
      ((Φ.continuous.measurable.comp q.measurable).mul p.measurable)
    intro t
    change |Φ (q t) * p t| ≤ ‖Φ‖
    rw [abs_mul, abs_of_nonneg (p.nonneg t)]
    exact (mul_le_mul_of_nonneg_left (p.le_one t) (abs_nonneg _)).trans
      (by simpa only [mul_one, Real.norm_eq_abs] using Φ.norm_coe_le_norm (q t))
  simp_rw [restrictedBlockOverlapPath_eq_average hN S hS h]
  conv_lhs => arg 2; ext t; rw [mul_left_comm, Finset.mul_sum]
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => hi j)]

theorem restricted_coordinate_averages_tendsto {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : ℕ → FieldStep)
    (q : ℕ → OverlapPath) (Φ : ℝ →ᵇ ℝ) (v : ℕ → Fin N → ℝ)
    (hcoord : ∀ j, Tendsto (fun r => v r j - ∫ t,
      Φ (q r t) * restrictedCoordinateOverlapPath hN S hS (h r) j t ∂pathMeasure)
      atTop (𝓝 0)) :
    Tendsto (fun r => (N : ℝ)⁻¹ * ∑ j, v r j -
      ∫ t, Φ (q r t) * restrictedBlockOverlapPath hN S hS (h r) t ∂pathMeasure)
      atTop (𝓝 0) := by
  have hs := (tendsto_finsetSum Finset.univ (fun j _ => hcoord j)).const_mul (N : ℝ)⁻¹
  simp only [Finset.sum_const_zero, mul_zero] at hs
  convert hs using 1
  funext r
  rw [restricted_block_test_eq_average, Finset.sum_sub_distrib]
  ring

end InvariantIsing

end

end OAI
