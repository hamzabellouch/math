import OAI.Geometry.RCD.Heat.HeatMassTail
import OAI.Geometry.RCD.Heat.ActualHeatMass

namespace OAI

/-! # Finite shell bounds for the full Bochner heat mass -/

open Set Metric MeasureTheory Function
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- The first N+1 shells partition exactly the corresponding outer ball. -/
theorem finite_dyadicShell_union (p : X) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    (⋃ j ∈ Finset.range (N + 1), dyadicShell p r j) = ball p (2 ^ N * r) := by
  have hm : Monotone (fun j : ℕ => ball p (2 ^ j * r)) := by
    intro j k hjk
    exact ball_subset_ball (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjk) hr)
  change (⋃ j ∈ Finset.range (N + 1), disjointed (fun j : ℕ => ball p (2 ^ j * r)) j) = _
  rw [biUnion_range_succ_disjointed, hm.partialSups_eq]

/-- Integrate finitely many controlled shells and use a single bound on
the exterior. This applies directly to singular finite mass measures. -/
theorem integral_le_finite_shell_mass (ν : Measure X) [IsFiniteMeasure ν]
    (p : X) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) {f : X → ℝ} (hf : Integrable f ν)
    (W : ℕ → ℝ) (hW : ∀ j, 0 ≤ W j)
    (hlocal : ∀ j ≤ N, ∀ᵐ z ∂ν.restrict (dyadicShell p r j), f z ≤ W j)
    {T : ℝ} (hT : 0 ≤ T)
    (htail : ∀ᵐ z ∂ν.restrict (ball p (2 ^ N * r))ᶜ, f z ≤ T) :
    (∫ z, f z ∂ν) ≤
      (∑ j ∈ Finset.range (N + 1), W j * ν.real (ball p (2 ^ j * r))) + T * ν.real univ := by
  have hpart := integral_biUnion_finset (μ := ν) (f := f) (Finset.range (N + 1))
    (fun j _ => measurableSet_dyadicShell p r j)
    ((disjoint_disjointed (fun j : ℕ => ball p (2 ^ j * r))).set_pairwise _)
    (fun _ _ => hf.integrableOn)
  rw [finite_dyadicShell_union p hr N] at hpart
  have hlocal' : (∫ z in ball p (2 ^ N * r), f z ∂ν) ≤
      ∑ j ∈ Finset.range (N + 1), W j * ν.real (ball p (2 ^ j * r)) := by
    rw [hpart]
    apply Finset.sum_le_sum
    intro j hj
    exact setIntegral_le_bound_mul_volume ν (dyadicShell_subset_ball p r j)
      (measure_ne_top _ _) hf.integrableOn (hW j)
      (hlocal j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  have hout := setIntegral_le_bound_mul_volume ν (subset_univ _)
    (measure_ne_top _ _) hf.integrableOn hT htail
  have he := integral_add_compl (μ := ν) (s := ball p (2 ^ N * r)) measurableSet_ball hf
  linarith

variable [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The shell bound controls the actual heat mass of the full positive
Bochner measure, not just an assumed density. -/
theorem cutoffHeatMass_le_finite_shells (M : PositiveBilinearMeasure X E)
    (p : X) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) (N : ℕ)
    (W : ℕ → ℝ) (hW : ∀ j, 0 ≤ W j)
    (hlocal : ∀ j ≤ N, ∀ z ∈ dyadicShell p r j, χ z * ker t p z ≤ W j)
    {T : ℝ} (hT : 0 ≤ T)
    (htail : ∀ z ∉ ball p (2 ^ N * r), χ z * ker t p z ≤ T) (v : E) :
    ⟪v, cutoffHeatMass μ hQ hk hχ hsχ M ht p v⟫_ℝ ≤
      (∑ j ∈ Finset.range (N + 1), W j * (M.measure v).real (ball p (2 ^ j * r))) +
        T * (M.measure v).real univ := by
  rw [cutoffHeatMass_energy]
  apply integral_le_finite_shell_mass (M.measure v) p hr N
    ((hχ.mul (hk.continuous_right t ht p)).integrable_of_hasCompactSupport hsχ.mul_right) W hW
  · intro j hj
    filter_upwards [ae_restrict_mem (measurableSet_dyadicShell p r j)] with z hz
    exact hlocal j hj z hz
  · exact hT
  · filter_upwards [ae_restrict_mem measurableSet_ball.compl] with z hz
    exact htail z hz

end RegularPointCoordinates

end

end OAI
