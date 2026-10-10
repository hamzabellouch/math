import OAI.NumberTheory.CubicMoment.Estimates.StructuredCutoffConsistency
import OAI.NumberTheory.CubicMoment.Estimates.SmoothNormPartition

namespace OAI

/-! Exact finite smooth decomposition of the original structured sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def structuredPrimeSum (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (coordinatePrimeSupport W X Z)).filter
      (fun z => IsCoprime z e),
    primeMomentCoefficient W X Z z*mellinPhase u (norm z)*cubicSymbol z (v*a*b^2)

lemma normPartitionWeight_scaled (x D : ℝ) {L : ℝ} (hL : L ≠ 0) (hD : D ≠ 0) :
    normPartitionWeight (x/(L*(D/2))) = normPartitionWeight (2*(x/L)/D) := by
  congr 1
  field_simp

lemma structuredPrimeSum_partition (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ)
    {L B : ℝ} (hL : 0 < L) (N : ℕ) (hN : 2*B ≤ (4/3:ℝ)^N)
    (hrange : ∀ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z),
      L ≤ norm z ∧ norm z ≤ B*L) :
    structuredPrimeSum a b v e u W X Z =
      ∑ k ∈ Finset.range N,
        structuredPrimeMomentAt a b v e u W X Z normPartitionWeight (L*((4/3:ℝ)^k/2)) := by
  unfold structuredPrimeSum structuredPrimeMomentAt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.mul_sum]
  have hr := hrange z (Finset.mem_filter.mp hz).1
  have hm := normPartitionWeight_partition
    (show 1 ≤ norm z/L by exact (le_div_iff₀ hL).mpr (by simpa using hr.1))
    (show norm z/L ≤ B by exact (div_le_iff₀ hL).mpr hr.2) hN
  have heq : (∑ k ∈ Finset.range N,
      normPartitionWeight (norm z/(L*((4/3:ℝ)^k/2)))) = 1 := by
    simp_rw [normPartitionWeight_scaled _ _ hL.ne' (pow_ne_zero _ (by norm_num : (4/3:ℝ) ≠ 0))]
    exact hm
  rw [heq,mul_one]

lemma structuredPrimeSum_partition_dyads (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ)
    {L B : ℝ} (hL : 0 < L) (N : ℕ) (hN : 2*B ≤ (4/3:ℝ)^N)
    (hrange : ∀ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z),
      L ≤ norm z ∧ norm z ≤ B*L)
    (hZ : ∀ k ∈ Finset.range N, L*((4/3:ℝ)^k/2) ≤ Z) :
    structuredPrimeSum a b v e u W X Z =
      ∑ k ∈ Finset.range N,
        structuredPrimeMoment a b v e u W X normPartitionWeight (L*((4/3:ℝ)^k/2)) := by
  rw [structuredPrimeSum_partition a b v e u W X Z hL N hN hrange]
  apply Finset.sum_congr rfl
  intro k hk
  exact structuredPrimeMomentAt_eq a b v e u W X
    (mul_pos hL (div_pos (pow_pos (by norm_num : (0:ℝ) < 4/3) _) (by norm_num)))
    (hZ k hk) normPartitionWeight (fun _ => normPartitionWeight_high)

lemma finite_piece_moment_on {α κ : Type*} [Fintype κ] (S : Finset α)
    (f : κ → α → ℂ) :
    (∑ a ∈ S, ‖∑ k, f k a‖^2) ≤ (Fintype.card κ:ℝ)*(∑ k, ∑ a ∈ S, ‖f k a‖^2) := by
  calc
    _ ≤ ∑ a ∈ S, (Fintype.card κ:ℝ)*(∑ k, ‖f k a‖^2) := by
      apply Finset.sum_le_sum
      intro a ha
      apply (pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_sum_le _ _) 2).trans
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : κ => (1:ℝ))
        (fun k => ‖f k a‖)
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

end CubicFirstMoment

end

end OAI
