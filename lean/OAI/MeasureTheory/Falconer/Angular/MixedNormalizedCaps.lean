import OAI.MeasureTheory.Falconer.Angular.MixedCapDenominator
import OAI.MeasureTheory.Falconer.Estimates.MixedComposition
import OAI.MeasureTheory.Falconer.Angular.NormalizedCaps

namespace OAI

/-! # Full mixed derivative bounds for the normalized cap partition

The denominator and its fixed smooth reciprocal are the actual functions
used by the cap partition. Their bounds depend on the dimension and order,
independently of the selected separated net and its radius.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem capReciprocal_ambient_derivatives (d k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ)
      (S : Finset (Sphere d)),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      ∀ w : Sphere d,
      ‖iteratedFDeriv ℝ k (capReciprocal δ hδ S) w‖ ≤ C*(δ⁻¹)^k := by
  choose B hB hBb using fun j => capDenominator_ambient_derivatives d j
  obtain ⟨C,hC,hCb⟩ := compact_iteratedFDeriv_bound
    (smoothReciprocal_contDiff 1 zero_lt_one)
    (isCompact_closedBall (0 : ℝ) (B 0)) k
  refine ⟨mixedCompositionBudget B k*C,
    mul_nonneg (mixedCompositionBudget_nonneg hB k) hC, ?_⟩
  intro δ hδ S hsep w
  have hmem : capDenominator δ hδ S w ∈ Metric.closedBall (0 : ℝ) (B 0) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa using hBb 0 δ hδ S hsep w
  exact mixed_composition_derivative_bound
    (capDenominator_contDiff hδ S).contDiffAt
    (smoothReciprocal_contDiff 1 zero_lt_one).contDiffAt hC k
    (fun j hj => hCb j hj _ hmem)
    (fun j _ _ => hBb j δ hδ S hsep w)

theorem normalizedCap_ambient_derivatives (d k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ)
      (S : Finset (Sphere d)),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      ∀ (c w : Sphere d),
      ‖iteratedFDeriv ℝ k (normalizedCap δ hδ S c) w‖ ≤ C*(δ⁻¹)^k := by
  choose B hB hBb using fun j => capBump_ambient_derivatives d j
  choose Q hQ hQb using fun j => capReciprocal_ambient_derivatives d j
  let A := ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*B j*Q (k-j)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB j)) (hQ _))
  refine ⟨A,hA,?_⟩
  intro δ hδ S hsep c w
  apply (norm_iteratedFDeriv_mul_le (capBump δ hδ c).contDiff
    (capReciprocal_contDiff hδ S) (w : Space d) (by simp : (k : ℕ∞ω) ≤ ∞)).trans
  change _ ≤ (∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*B j*Q (k-j))*(δ⁻¹)^k
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ ≤ (k.choose j : ℝ)*(B j*(δ⁻¹)^j)*(Q (k-j)*(δ⁻¹)^(k-j)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hBb j δ hδ c w) (Nat.cast_nonneg _))
        (hQb (k-j) δ hδ S hsep w) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hB j) (by positivity)))
    _ = _ := by
      have hp : (δ⁻¹)^j*(δ⁻¹)^(k-j) = (δ⁻¹)^k := by
        rw [← pow_add,Nat.add_sub_of_le hjk]
      calc
        _ = ((k.choose j : ℝ)*B j*Q (k-j))*((δ⁻¹)^j*(δ⁻¹)^(k-j)) := by ring
        _ = _ := by rw [hp]

end Falconer

end OAI
