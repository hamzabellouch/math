import OAI.NumberTheory.JointDickman.Arithmetic.MertensDischarge
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeIntervalSums

namespace OAI

/-! # Uniform reciprocal-prime mass on multiplicative intervals -/
namespace JointDickman
open Finset

/-- The proved Mertens remainder controls any prime interval by its
multiplicative width and the logarithm of its lower endpoint. -/
theorem prime_reciprocal_interval_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ L U R : ℝ, 2 ≤ L → L ≤ U → 1 ≤ R → U ≤ R*L →
      (∑ p ∈ largePrimeSet U L, 1/(p:ℝ)) ≤ (Real.log R+C)/Real.log L := by
  obtain ⟨M,C,hC,hM⟩ := primeReciprocalMertensInput
  refine ⟨2*C,by positivity,?_⟩
  intro L U R hL hLU hR hU
  have hL0 : 0 < L := by linarith
  have hU0 : 0 < U := hL0.trans_le hLU
  have hR0 : 0 < R := by linarith
  have hl : 0 < Real.log L := Real.log_pos (by linarith)
  have hu : 0 < Real.log U := Real.log_pos (by linarith)
  have hlu : Real.log L ≤ Real.log U := Real.log_le_log hL0 hLU
  have hmL := hM L hL
  have hmU := hM U (hL.trans hLU)
  simp only [← primesLE_eq_filter] at hmL hmU
  change |primeReciprocalSum L-Real.log (Real.log L)-M| ≤ C/Real.log L at hmL
  change |primeReciprocalSum U-Real.log (Real.log U)-M| ≤ C/Real.log U at hmU
  have herror : C/Real.log U ≤ C/Real.log L := div_le_div_of_nonneg_left hC hl hlu
  have hlog : Real.log (Real.log U)-Real.log (Real.log L) ≤ Real.log R/Real.log L := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hu hl)
    rw [Real.log_div hu.ne' hl.ne'] at h1
    have h2 := Real.log_le_log hU0 hU
    rw [Real.log_mul hR0.ne' hL0.ne'] at h2
    have h3 : Real.log U/Real.log L-1 ≤ Real.log R/Real.log L := by
      calc
        _ = (Real.log U-Real.log L)/Real.log L := by field_simp
        _ ≤ Real.log R/Real.log L := div_le_div_of_nonneg_right (by linarith) hl.le
    exact h1.trans h3
  rw [largePrimeSet_reciprocal_eq hL0.le hLU]
  have hLo := (abs_le.mp hmL).1
  have hHi := (abs_le.mp hmU).2
  calc
    _ ≤ (Real.log (Real.log U)-Real.log (Real.log L))+2*C/Real.log L := by
      have he : 2*C/Real.log L = C/Real.log L+C/Real.log L := by ring
      rw [he]
      linarith
    _ ≤ Real.log R/Real.log L+2*C/Real.log L := add_le_add hlog le_rfl
    _ = _ := by ring

/-- The same bound for an arbitrary subset of such a prime interval. -/
theorem prime_reciprocal_interval_subset : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : Finset ℕ) (L U R : ℝ), 2 ≤ L → 1 ≤ R → U ≤ R*L →
      (∀ p ∈ P, p.Prime ∧ L < (p:ℝ) ∧ (p:ℝ) ≤ U) →
      (∑ p ∈ P, 1/(p:ℝ)) ≤ (Real.log R+C)/Real.log L := by
  obtain ⟨C,hC,hbound⟩ := prime_reciprocal_interval_bound
  refine ⟨C,hC,?_⟩
  intro P L U R hL hR hU hP
  by_cases hLU : L ≤ U
  · apply le_trans (b := ∑ p ∈ largePrimeSet U L, 1/(p:ℝ))
    · apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
      intro p hp
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr
        ⟨Nat.le_floor (hP p hp).2.2,(hP p hp).1⟩,(hP p hp).2.1⟩
    · exact hbound L U R hL hLU hR hU
  · have he : P = ∅ := eq_empty_iff_forall_notMem.mpr (by
      intro p hp
      exact hLU (le_trans (hP p hp).2.1.le (hP p hp).2.2))
    rw [he,sum_empty]
    exact div_nonneg (add_nonneg (Real.log_nonneg hR) hC) (Real.log_nonneg (by linarith))

end JointDickman

end OAI
