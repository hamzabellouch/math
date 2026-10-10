import OAI.Combinatorics.DiscreteConvexity.CoveringPairCost
import OAI.Combinatorics.DiscreteConvexity.CoveringResidualCost
import OAI.Combinatorics.DiscreteConvexity.ProbabilisticExistence

namespace OAI

/-!
# The elementary covering lemma

The initial generators and regular edges are constructed from weighted
degrees. The remaining generators come from an actual finite Bernoulli
sample of ordered pairs. Every outcome is a containment cover, and finite
averaging selects an outcome meeting the claimed cost budget.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem elementary_covering (H : Family V) (rho : ℝ) (r h : ℕ)
    (hrho0 : 0 < rho) (_hrho1 : rho < 1)
    (uniform : ∀ e ∈ H, e.card = r)
    (_hr : 1 ≤ r) (hrh : r ≤ h) (hh : 64 ≤ h)
    (hweight : (H.card : ℝ) * rho ^ r ≤ (2 : ℝ) ^ (h + 1)) :
    ∃ G : Family V, Covers G (denseFamily H (2 ^ (12 * h))) ∧
      cost rho G ≤ 3 * ((2 : ℝ) ^ h)⁻¹ := by
  classical
  let T := NumericalBounds.T h
  let m := NumericalBounds.m h
  let p := NumericalBounds.p h
  let C0 := initialFamily H rho r T
  let K := regularEdges H rho r T
  let μ := bernoulliLaw (α := PairIndex K) p
    (NumericalBounds.p_nonneg h) (NumericalBounds.p_le_one h)
  let G : Sample K → Family V := fun sample =>
    C0 ∪ sampledFamily K sample ∪ residualFamily K m sample
  have hrho : 0 ≤ rho := hrho0.le
  have hT : 0 ≤ T := NumericalBounds.T_nonneg h
  have hK : K ⊆ H := regularEdges_subset H rho r T
  have hKuniform : ∀ e ∈ K, e.card = r := fun e he => uniform e (hK he)
  have hcover (sample : Sample K) : Covers (G sample) (denseFamily H m) :=
    covers_sampled_residual H C0 m sample
  have hC0 : cost rho C0 ≤ 2 * ((2 : ℝ) ^ (2 * h))⁻¹ := by
    calc
      cost rho C0 ≤ T⁻¹ * (2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r :=
        initial_cost_le hrho (NumericalBounds.T_pos h) uniform
      _ = (T⁻¹ * (2 : ℝ) ^ r) * ((H.card : ℝ) * rho ^ r) := by ring
      _ ≤ (T⁻¹ * (2 : ℝ) ^ r) * (2 : ℝ) ^ (h + 1) :=
        mul_le_mul_of_nonneg_left hweight
          (mul_nonneg (inv_nonneg.mpr hT) (pow_nonneg (by norm_num) _))
      _ ≤ 2 * ((2 : ℝ) ^ (2 * h))⁻¹ := NumericalBounds.initial_cost_le r h hrh
  have hC1 : μ.expectation (fun sample => cost rho (sampledFamily K sample)) ≤
      2 * ((2 : ℝ) ^ (2 * h))⁻¹ := by
    calc
      μ.expectation (fun sample => cost rho (sampledFamily K sample)) ≤
          p * ((H.card : ℝ) * rho ^ r * (2 : ℝ) ^ r * T) :=
        expectation_sampledFamily_le hrho hT uniform
          (NumericalBounds.p_nonneg h) (NumericalBounds.p_le_one h)
      _ = (p * (2 : ℝ) ^ r * T) * ((H.card : ℝ) * rho ^ r) := by ring
      _ ≤ (p * (2 : ℝ) ^ r * T) * (2 : ℝ) ^ (h + 1) :=
        mul_le_mul_of_nonneg_left hweight
          (mul_nonneg (mul_nonneg (NumericalBounds.p_nonneg h)
            (pow_nonneg (by norm_num) _)) hT)
      _ = p * (2 : ℝ) ^ (h + 1) * (2 : ℝ) ^ r * T := by ring
      _ ≤ 2 * ((2 : ℝ) ^ (2 * h))⁻¹ := NumericalBounds.pair_cost_le r h hrh
  have hC2 : μ.expectation (fun sample => cost rho (residualFamily K m sample)) ≤
      ((2 : ℝ) ^ m)⁻¹ :=
    expectation_residualFamily_le_inv_pow K hrho hKuniform
      (fun B => regular_extension_le_pow hrho hT uniform B) hrh hh
  have hmean : μ.expectation (fun sample => cost rho (G sample)) ≤
      3 * ((2 : ℝ) ^ h)⁻¹ := by
    calc
      μ.expectation (fun sample => cost rho (G sample)) ≤
          μ.expectation (fun sample => cost rho C0 +
            cost rho (sampledFamily K sample) + cost rho (residualFamily K m sample)) := by
        apply μ.expectation_mono
        intro sample
        exact (cost_union_le hrho (C0 ∪ sampledFamily K sample)
          (residualFamily K m sample)).trans
            (add_le_add (cost_union_le hrho C0 (sampledFamily K sample)) le_rfl)
      _ = cost rho C0 + μ.expectation (fun sample => cost rho (sampledFamily K sample)) +
          μ.expectation (fun sample => cost rho (residualFamily K m sample)) := by
        rw [μ.expectation_add, μ.expectation_add, μ.expectation_const]
      _ ≤ 4 * ((2 : ℝ) ^ (2 * h))⁻¹ + ((2 : ℝ) ^ m)⁻¹ := by
        linarith
      _ ≤ 3 * ((2 : ℝ) ^ h)⁻¹ := NumericalBounds.final_cost_le h hh
  obtain ⟨sample, hsample⟩ := μ.exists_le_expectation (fun sample => cost rho (G sample))
  exact ⟨G sample, hcover sample, hsample.trans hmean⟩

end TalagrandDiscreteConvexity.Covering

end OAI
