import OAI.Combinatorics.DiscreteConvexity.CoveringSampledFamilies
import OAI.Combinatorics.DiscreteConvexity.CoveringResidualProbability
import OAI.Combinatorics.DiscreteConvexity.CoveringResidualTuples
import OAI.Combinatorics.DiscreteConvexity.CoveringNumericalBounds

namespace OAI

/-!
# Expected cost of the actual residual generators

Repeated unions are first counted with multiplicity. Each injective tuple
avoids exactly its distinct ordered-pair indices under the product Bernoulli
law. Finite linearity then separates this common survival probability from
the weighted tuple sum.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators Classical

variable {V : Type*} [DecidableEq V]

/-- The expected residual cost is bounded by the actual weighted tuple sum
times the exact probability of avoiding all ordered pairs of one tuple. -/
theorem expectation_residualFamily_le (H : Family V) (rho : ℝ)
    (hrho : 0 ≤ rho) (m : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliLaw (α := PairIndex H) p hp0 hp1).expectation
        (fun sample => cost rho (residualFamily H m sample)) ≤
      tupleWeightSum H rho m * (1 - p) ^ (m * m) := by
  classical
  let μ := bernoulliLaw (α := PairIndex H) p hp0 hp1
  calc
    μ.expectation (fun sample => cost rho (residualFamily H m sample)) ≤
        μ.expectation (fun sample => ∑ f : EdgeTuple H m,
          if Disjoint sample (tuplePairs f) then rho ^ (tupleUnion f).card else 0) :=
      μ.expectation_mono (fun sample => cost_residualFamily_le H m sample hrho)
    _ = ∑ f : EdgeTuple H m, μ.expectation (fun sample =>
          if Disjoint sample (tuplePairs f) then rho ^ (tupleUnion f).card else 0) :=
      μ.expectation_sum _
    _ = ∑ f : EdgeTuple H m, (1 - p) ^ (m * m) * rho ^ (tupleUnion f).card := by
      apply Finset.sum_congr rfl
      intro f _
      calc
        μ.expectation (fun sample => if Disjoint sample (tuplePairs f)
            then rho ^ (tupleUnion f).card else 0) =
            μ.prob (fun sample => Disjoint sample (tuplePairs f)) *
              rho ^ (tupleUnion f).card := by
          simp only [FiniteLaw.expectation, FiniteLaw.prob, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro sample _
          by_cases hs : Disjoint sample (tuplePairs f)
          · simp only [ite_eq_left hs]
          · simp only [ite_eq_right hs, mul_zero, zero_mul]
        _ = _ := congrArg (fun q : ℝ => q * rho ^ (tupleUnion f).card)
          (tuple_survival_probability f p hp0 hp1)
    _ = tupleWeightSum H rho m * (1 - p) ^ (m * m) := by
      unfold tupleWeightSum tupleWeight
      rw [← Finset.mul_sum]
      exact mul_comm _ _

/-- Applying the proved tuple recurrence bounds the expected residual cost
using only the actual extension estimate for the edge family. -/
theorem expectation_residualFamily_le_extension (H : Family V)
    {rho T : ℝ} {r m : ℕ} (hrho : 0 ≤ rho) (hT : 0 ≤ T)
    (uniform : ∀ e ∈ H, (e : Finset V).card = r)
    (extension : ∀ B : Finset V,
      (∑ e ∈ H, rho ^ (e \ B).card) ≤ T * (1 + (B.card : ℝ)) ^ r)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliLaw (α := PairIndex H) p hp0 hp1).expectation
        (fun sample => cost rho (residualFamily H m sample)) ≤
      (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) ^ m * (1 - p) ^ (m * m) := by
  exact (expectation_residualFamily_le H rho hrho m p hp0 hp1).trans
    (mul_le_mul_of_nonneg_right
      (tupleWeightSum_le H (rho := rho) (T := T) (r := r) (m := m)
        hrho hT uniform extension)
      (pow_nonneg (sub_nonneg.mpr hp1) _))

theorem expectation_residualFamily_le_inv_pow (H : Family V)
    {rho : ℝ} {r h : ℕ} (hrho : 0 ≤ rho)
    (uniform : ∀ e ∈ H, (e : Finset V).card = r)
    (extension : ∀ B : Finset V, (∑ e ∈ H, rho ^ (e \ B).card) ≤
      NumericalBounds.T h * (1 + (B.card : ℝ)) ^ r)
    (hrh : r ≤ h) (hh : 64 ≤ h) :
    (bernoulliLaw (α := PairIndex H) (NumericalBounds.p h)
      (NumericalBounds.p_nonneg h) (NumericalBounds.p_le_one h)).expectation
        (fun sample => cost rho (residualFamily H (NumericalBounds.m h) sample)) ≤
      ((2 : ℝ) ^ NumericalBounds.m h)⁻¹ := by
  have hbound := expectation_residualFamily_le_extension H
    (rho := rho) (r := r) (m := NumericalBounds.m h) hrho
    (NumericalBounds.T_nonneg h) uniform extension (NumericalBounds.p h)
    (NumericalBounds.p_nonneg h) (NumericalBounds.p_le_one h)
  apply hbound.trans
  simpa only [Nat.cast_mul] using NumericalBounds.residual_cost_le_inv_pow r h hrh hh

end TalagrandDiscreteConvexity.Covering

end OAI
