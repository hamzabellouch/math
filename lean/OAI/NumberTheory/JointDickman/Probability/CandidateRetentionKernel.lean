import OAI.NumberTheory.JointDickman.Amplification.CandidateFairArithmetic
import OAI.NumberTheory.JointDickman.Probability.RemainderKernelEstimate

namespace OAI

/-! # The candidate coefficient weight for the remainder-regularity estimate -/

namespace JointDickman
open Finset

open Classical in
noncomputable def candidateRetainedWeight (B L j : ℕ) (τ C : ℝ) (T V : ℕ)
    (A D : Finset ℕ) : ℝ :=
  if RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D then
    B*∑ c ∈ Ioc 0 V, regularArithmeticScalar B L j τ C T c (∏ p ∈ A,p) (∏ p ∈ D,p)
  else 0

open Classical in
theorem regularRetainedArithmeticKernel_eq (B L j : ℕ) (τ C : ℝ) (T V : ℕ)
    (S R : Finset ℕ) :
    regularRetainedArithmeticKernel B L j τ C T V S R =
      regularRemainderKernel B L τ C (candidateRetainedWeight B L j τ C T V) S R := by
  unfold regularRetainedArithmeticKernel regularRemainderKernel candidateRetainedWeight
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro D _
  have he : ((RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A)) ∧
      (RegularPrimeSet B L τ C D ∧ RegularPrimeSet B L τ C (R \ D))) =
      ((RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D) ∧
      (RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D))) := by
    apply propext
    tauto
  simp_rw [he]
  by_cases hs : RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D
  all_goals by_cases hr : RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D)
  all_goals simp only [hs,hr,and_self,and_false,false_and,ite_true,ite_false,
    mul_zero,sum_const_zero]
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro c _
  ring

open Classical in
theorem candidateRetainedWeight_bounds (B L j : ℕ) (τ C : ℝ) (T V : ℕ) (A D : Finset ℕ) :
    0 ≤ candidateRetainedWeight B L j τ C T V A D ∧
      candidateRetainedWeight B L j τ C T V A D ≤
        amplificationProductWeight B j T V (∏ p ∈ D,p) (∏ p ∈ A,p) := by
  have hscalar (c : ℕ) :
      0 ≤ regularArithmeticScalar B L j τ C T c (∏ p ∈ A,p) (∏ p ∈ D,p) ∧
      regularArithmeticScalar B L j τ C T c (∏ p ∈ A,p) (∏ p ∈ D,p) ≤
        amplificationScalarWeight B j T c (∏ p ∈ A,p) (∏ p ∈ D,p) := by
    unfold regularArithmeticScalar
    split_ifs
    · exact ⟨(amplificationScalarWeight_bounds ..).1,le_rfl⟩
    · exact ⟨le_rfl,(amplificationScalarWeight_bounds ..).1⟩
  unfold candidateRetainedWeight amplificationProductWeight
  split_ifs
  · exact ⟨mul_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun c _ => (hscalar c).1)),
      mul_le_mul_of_nonneg_left (sum_le_sum (fun c _ => (hscalar c).2)) (Nat.cast_nonneg _)⟩
  · exact ⟨le_rfl,mul_nonneg (Nat.cast_nonneg _)
      (sum_nonneg (fun c _ => (amplificationScalarWeight_bounds ..).1))⟩

open Classical in
theorem candidateRetainedWeight_support {B L j T V : ℕ} {τ C : ℝ}
    (hB : 30 ≤ B) (hT : 0 < T) (hlogT : Real.log T ≤ (B : ℝ)/10)
    {A D : Finset ℕ} (hw : candidateRetainedWeight B L j τ C T V A D ≠ 0) :
    (∏ p ∈ A,p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      (∏ p ∈ D,p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) := by
  have hweight := candidateRetainedWeight_bounds B L j τ C T V A D
  have hprod : amplificationProductWeight B j T V (∏ p ∈ D,p) (∏ p ∈ A,p) ≠ 0 := by
    intro hz
    exact hw (le_antisymm (hweight.2.trans_eq hz) hweight.1)
  unfold amplificationProductWeight at hprod
  obtain ⟨c,hc,hcne⟩ := exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hprod)
  obtain ⟨_,_,_,hclog,hlo,hhi,ha,had,_⟩ := amplificationScalarWeight_support
    (show 0 < B by omega) hT (mem_Ioc.mp hc).1 hcne
  have hBr : (30 : ℝ) ≤ B := by exact_mod_cast hB
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hcr : (0 : ℝ) < c := by exact_mod_cast (mem_Ioc.mp hc).1
  have hTexp : (T : ℝ) ≤ Real.exp ((B : ℝ)/10) := by
    rw [← Real.exp_log hTr]
    exact Real.exp_le_exp.mpr hlogT
  have hcexp : (c : ℝ) ≤ Real.exp (2*(B : ℝ)) := by
    rw [← Real.exp_log hcr]
    exact Real.exp_le_exp.mpr hclog
  have htwo : (2 : ℝ) ≤ Real.exp ((11/10 : ℝ)*B) := by
    have hh := Real.add_one_le_exp ((11/10 : ℝ)*B)
    linarith
  have hupper : (2*T*c : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) := by
    have hh : (2 : ℝ)*T*c ≤
        Real.exp ((11/10 : ℝ)*B)*Real.exp ((B : ℝ)/10)*Real.exp (2*(B : ℝ)) :=
      mul_le_mul (mul_le_mul htwo hTexp (Nat.cast_nonneg _) (Real.exp_pos _).le)
        hcexp (Nat.cast_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    have he : Real.exp ((11/10 : ℝ)*B)*Real.exp ((B : ℝ)/10)*Real.exp (2*(B : ℝ)) =
        Real.exp ((16/5 : ℝ)*B) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    rw [he] at hh
    exact_mod_cast hh
  exact ⟨(by exact_mod_cast hhi : ((∏ p ∈ A,p : ℕ) : ℝ) ≤ (2*T*c : ℕ)).trans hupper,
    (by exact_mod_cast had : ((∏ p ∈ D,p : ℕ) : ℝ) ≤ (2*T*c : ℕ)).trans hupper⟩

end JointDickman

end OAI
