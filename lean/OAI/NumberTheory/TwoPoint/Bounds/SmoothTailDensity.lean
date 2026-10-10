import OAI.NumberTheory.TwoPoint.Bounds.TruncatedDilation
import OAI.NumberTheory.TwoPoint.Bounds.SmoothReciprocalMass

namespace OAI

/-! The density discarded by truncating the smooth part of an integer.
The bound retains the exact half-power Euler cost of the dilation. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma reciprocal_smooth_tail (P A : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (K : ℝ) (hK : 0 < K) (hA : ∀ a ∈ A, a ∈ Nat.factoredNumbers P)
    (hlarge : ∀ a ∈ A, K ≤ (a : ℝ)) :
    (∑ a ∈ A, 1 / (a : ℝ)) ≤
      K ^ (-(1 / 2) : ℝ) * smoothReciprocalProduct P (1 / 2 : ℝ) := by
  calc
    _ ≤ ∑ a ∈ A, K ^ (-(1 / 2) : ℝ) * (a : ℝ) ^ (-(1 / 2) : ℝ) := by
      apply sum_le_sum
      intro a ha
      have hap : (0 : ℝ) < a := hK.trans_le (hlarge a ha)
      have he : 1 / (a : ℝ) = (a : ℝ) ^ (-(1 / 2) : ℝ) *
          (a : ℝ) ^ (-(1 / 2) : ℝ) := by
        rw [← Real.rpow_add hap]
        norm_num [Real.rpow_neg_one]
      rw [he]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hK (hlarge a ha) (by norm_num)) (by positivity)
    _ = K ^ (-(1 / 2) : ℝ) * ∑ a ∈ A, (a : ℝ) ^ (-(1 / 2) : ℝ) :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (smooth_reciprocal_sum_le P A hP (1 / 2) (by norm_num) hA) (by positivity)

lemma smooth_part_tail_density (q K N : ℕ) (hK : 0 < K) :
    (∑ v ∈ range N, if K < primeSmoothPart q.primeFactors (v + 1)
      then (1 : ℝ) else 0) ≤
      (N : ℝ) * (K : ℝ) ^ (-(1 / 2) : ℝ) *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  let A := (Icc (K + 1) N).filter (fun a => a.primeFactors ⊆ q.primeFactors)
  have hA (a : ℕ) (ha : a ∈ A) : 0 < a := by
    have hh := (mem_Icc.mp (mem_filter.mp ha).1).1
    omega
  have hsum : (∑ v ∈ range N, if K < primeSmoothPart q.primeFactors (v + 1)
      then (1 : ℝ) else 0) ≤ ∑ a ∈ A, ((N / a : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ v ∈ range N, ∑ a ∈ A, if a ∣ v + 1 then (1 : ℝ) else 0 := by
        apply sum_le_sum
        intro v hv
        apply (smoothPart_tail_indicator q (v + 1) K (by omega)).trans
        apply sum_le_sum_of_subset_of_nonneg
        · intro a ha
          obtain ⟨ha, hs⟩ := mem_filter.mp ha
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp ha).1,
            (mem_Icc.mp ha).2.trans (by have hv' := mem_range.mp hv; omega)⟩, hs⟩
        · intro a _ _
          split_ifs <;> positivity
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro a _
        have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.card_multiples N a)
        simpa only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
          Nat.cast_zero] using hh
  have hmass := reciprocal_smooth_tail q.primeFactors A
    (fun p hp => Nat.prime_of_mem_primeFactors hp) (K : ℝ)
    (by exact_mod_cast hK)
    (fun a ha => Nat.mem_factoredNumbers_of_primeFactors_subset (hA a ha).ne'
      (mem_filter.mp ha).2)
    (fun a ha => by exact_mod_cast (show K ≤ a by
      have hh := (mem_Icc.mp (mem_filter.mp ha).1).1; omega))
  calc
    _ ≤ ∑ a ∈ A, ((N / a : ℕ) : ℝ) := hsum
    _ ≤ ∑ a ∈ A, (N : ℝ) / a := sum_le_sum (fun _ _ => Nat.cast_div_le)
    _ = (N : ℝ) * ∑ a ∈ A, 1 / (a : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg N)).trans_eq (by ring)

end TwoPointCorrelations

end OAI
