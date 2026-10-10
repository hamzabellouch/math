import OAI.NumberTheory.JointDickman.Probability.AmplificationTensorProfile

namespace OAI

/-! # Exact dyadic recombination of the original amplification weight -/

namespace JointDickman
open Finset

noncomputable def dyadicBoxIndices (L U : ℕ) : Finset ℤ :=
  (Ico L U).image (fun k => ((k+1 : ℕ) : ℤ))

theorem exp_nat_log_two (k : ℕ) : Real.exp ((k : ℝ)*Real.log 2) = (2 : ℝ)^k := by
  rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem geometric_dyadic_partition {L U : ℕ} (hLU : L ≤ U) (z : ℝ)
    (hlo : 2 ≤ z/(2 : ℝ)^L) (hhi : z/(2 : ℝ)^U ≤ 1) :
    (∑ k ∈ dyadicBoxIndices L U, dyadicPartitionWeight (z/Real.exp ((k : ℝ)*Real.log 2))) = 1 := by
  classical
  rw [dyadicBoxIndices,sum_image]
  · simpa only [Int.cast_natCast,exp_nat_log_two] using dyadicPartition_sum hLU z hlo hhi
  · intro a _ b _ h
    exact Nat.add_right_cancel (Int.ofNat_inj.mp h)

theorem amplificationBoxWeight_normalized (B : ℕ) {T N c : ℝ}
    (hT : 0 < T) (hN : 0 < N) (hc : 0 < c) (a b : ℝ) :
    amplificationBoxWeight B (Real.log (N/T)/B) (a/N) (b/N) (c/(N/T)) =
      amplificationBump (Real.log c/B)*amplificationBump (a/(T*c))*
        amplificationBump (b/(T*c))*dyadicPartitionWeight (c/(N/T)) := by
  have hX := div_pos hN hT
  have hlog : Real.log (N/T)/B+Real.log (c/(N/T))/B = Real.log c/B := by
    rw [Real.log_div hc.ne' hX.ne']
    ring
  have ha : (a/N)/(c/(N/T)) = a/(T*c) := by field_simp
  have hb : (b/N)/(c/(N/T)) = b/(T*c) := by field_simp
  simp only [amplificationBoxWeight,amplificationSpatialProfile,hlog,ha,hb]
  ring

theorem amplificationBoxWeight_dyadic_sum (B : ℕ) {T c : ℝ} (hT : 0 < T) (hc : 0 < c)
    (a b : ℝ) {L U : ℕ} (hLU : L ≤ U)
    (hlo : 2 ≤ (c*T)/(2 : ℝ)^L) (hhi : (c*T)/(2 : ℝ)^U ≤ 1) :
    (∑ k ∈ dyadicBoxIndices L U,
      amplificationBoxWeight B (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B)
        (a/Real.exp ((k : ℝ)*Real.log 2)) (b/Real.exp ((k : ℝ)*Real.log 2))
        (c/(Real.exp ((k : ℝ)*Real.log 2)/T))) =
      amplificationBump (Real.log c/B)*amplificationBump (a/(T*c))*
        amplificationBump (b/(T*c)) := by
  simp_rw [amplificationBoxWeight_normalized B hT (Real.exp_pos _) hc a b,
    div_div_eq_mul_div]
  rw [← mul_sum,geometric_dyadic_partition hLU (c*T) hlo hhi,mul_one]

end JointDickman

end OAI
