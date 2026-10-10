import OAI.NumberTheory.JointDickman.Probability.CandidateFairSplit
import OAI.NumberTheory.JointDickman.Amplification.ArithmeticCandidateWeight
import OAI.NumberTheory.JointDickman.Amplification.AmplificationWeightBound
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductGcdError

namespace OAI

/-! # Identifying the arithmetic scalar with an admissible candidate -/

namespace JointDickman
open Finset

/-- The candidate quotient is the unique coefficient in its additive relation. -/
theorem candidateQuotient_of_relation {M : ℕ} {e : BlockCandidateIndex M} {c : ℕ}
    (hj : 0 < candidateLag e)
    (he : candidateHigh e = candidateLow e+candidateLag e*c) :
    candidateQuotient e = c := by
  unfold candidateQuotient
  rw [he,Nat.add_sub_cancel_left,Nat.mul_div_cancel_left c hj]

open Classical in
theorem amplificationScalarWeight_support {B j T c b a : ℕ}
    (hB : 0 < B) (hT : 0 < T) (hc : 0 < c)
    (hw : amplificationScalarWeight B j T c b a ≠ 0) :
    a = b+j*c ∧ coefficientWeight B c ≠ 0 ∧
      (B : ℝ) ≤ Real.log c ∧ Real.log c ≤ 2*B ∧
      T*c ≤ b ∧ b ≤ 2*T*c ∧ T*c ≤ a ∧ a ≤ 2*T*c ∧
      c = ∏ p ∈ coefficientPrimeSet B c,p := by
  have he : a = b+j*c := by
    by_contra h
    exact hw (by simp [amplificationScalarWeight,h])
  rw [amplificationScalarWeight,ite_eq_left he] at hw
  obtain ⟨hcoef,hprod⟩ := mul_ne_zero_iff.mp hw
  obtain ⟨hprod,hb⟩ := mul_ne_zero_iff.mp hprod
  obtain ⟨hlog,ha⟩ := mul_ne_zero_iff.mp hprod
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hTC : (0 : ℝ) < T*c := by positivity
  have hl := amplificationBump_support hlog
  have hla := amplificationBump_support ha
  have hlb := amplificationBump_support hb
  have hloglo : (B : ℝ) ≤ Real.log c := by
    have := (lt_div_iff₀ hBr).mp hl.1
    linarith
  have hloghi : Real.log c ≤ 2*B := ((div_lt_iff₀ hBr).mp hl.2).le
  have hlo (n : ℕ) (h : 1 < (n : ℝ)/(T*c)) : T*c ≤ n := by
    have := (lt_div_iff₀ hTC).mp h
    have hn : (T : ℝ)*c ≤ n := by simpa only [one_mul] using this.le
    exact_mod_cast hn
  have hhi (n : ℕ) (h : (n : ℝ)/(T*c) < 2) : n ≤ 2*T*c := by
    have hh := (div_lt_iff₀ hTC).mp h
    have hn : (n : ℝ) ≤ 2*(T : ℝ)*c := by simpa only [mul_assoc] using hh.le
    exact_mod_cast hn
  refine ⟨he,hcoef,hloglo,hloghi,hlo b hlb.1,hhi b hlb.2,
    hlo a hla.1,hhi a hla.2,?_⟩
  apply coefficientWeight_eq_primeProduct hcoef
  change (c : ℝ) ≤ Real.exp (4*(B : ℝ))
  rw [← Real.exp_log hcr]
  apply Real.exp_le_exp.mpr
  linarith

open Classical in
/-- Once the three retained coefficients are regular and the endpoints are
coprime, every nonzero smooth arithmetic summand is an actual candidate. -/
theorem candidateAdmissible_of_scalar {B L T H M c : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hc : 0 < c)
    {i t : Fin M} (hit : i < t) {A D : Finset ℕ}
    (hH : H < t.val-i.val) (hjT : t.val-i.val < T)
    (hw : amplificationScalarWeight B (t.val-i.val) T c
      (∏ p ∈ A,p) (∏ p ∈ D,p) ≠ 0)
    (hcop : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p))
    (hreg : RegularPrimeSet B L τ C (coefficientPrimeSet B c)) :
    BlockCandidateAdmissible B L T H τ C ((i,t),(A,D)) := by
  obtain ⟨he,hcoef,hlo,hhi,hbl,hbu,hal,hau,hprod⟩ :=
    amplificationScalarWeight_support hB hT hc hw
  have hj : 0 < candidateLag ((i,t),(A,D)) := by
    change 0 < t.val-i.val
    exact Nat.sub_pos_of_lt hit
  have heq : candidateHigh ((i,t),(A,D)) =
      candidateLow ((i,t),(A,D))+candidateLag ((i,t),(A,D))*c := he
  have hq := candidateQuotient_of_relation hj heq
  have hcop' := (additive_triple_coprime_iff he).mpr hcop.symm
  unfold BlockCandidateAdmissible
  rw [hq]
  exact ⟨hit,hH,hjT,hc,heq,hcop,hcop'.2.2,hcop'.2.1,hprod,hreg,
    hlo,hhi,hbl,hbu,hal,hau⟩


open Classical in
noncomputable def regularCandidateScalar {M : ℕ} (B L T H : ℕ) (τ C : ℝ)
    (e : BlockCandidateIndex M) : ℝ :=
  if BlockCandidateAdmissible B L T H τ C e then
    regularCoefficientWeight B L τ C (candidateQuotient e)*
      candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e
  else 0

open Classical in
/-- The candidate restrictions impose no extra condition on a nonzero
smooth summand once coprimality and coefficient regularity are retained. -/
theorem regularCandidateScalar_eq_of_relation {B L T H M c : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hc : 0 < c)
    {i t : Fin M} (hit : i < t) {A D : Finset ℕ}
    (hH : H < t.val-i.val) (hjT : t.val-i.val < T)
    (he : (∏ p ∈ D,p) = (∏ p ∈ A,p)+(t.val-i.val)*c) :
    regularCandidateScalar B L T H τ C ((i,t),(A,D)) =
      if (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) ∧
          RegularPrimeSet B L τ C (coefficientPrimeSet B c) then
        amplificationScalarWeight B (t.val-i.val) T c (∏ p ∈ A,p) (∏ p ∈ D,p)
      else 0 := by
  have hj : 0 < candidateLag ((i,t),(A,D)) := Nat.sub_pos_of_lt hit
  have hq : candidateQuotient ((i,t),(A,D)) = c := candidateQuotient_of_relation hj he
  have hcut : candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T)
      ((i,t),(A,D)) =
      amplificationBump (Real.log c/B)*amplificationBump ((∏ p ∈ D,p : ℕ)/(T*c : ℝ))*
        amplificationBump ((∏ p ∈ A,p : ℕ)/(T*c : ℝ)) := by
    simp only [candidateCutoff,amplificationOuterWeight,amplificationInnerWeight,
      hq,candidateHigh,candidateLow]
  by_cases ha : BlockCandidateAdmissible B L T H τ C ((i,t),(A,D))
  · have hp : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) ∧
        RegularPrimeSet B L τ C (coefficientPrimeSet B c) := by
      exact ⟨ha.2.2.2.2.2.1,by simpa only [hq] using ha.2.2.2.2.2.2.2.2.2.1⟩
    rw [regularCandidateScalar,ite_eq_left ha,ite_eq_left hp,hq,hcut,
      regularCoefficientWeight,ite_eq_left hp.2,
      amplificationScalarWeight,ite_eq_left he]
  · rw [regularCandidateScalar,ite_eq_right ha]
    by_cases hp : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) ∧
        RegularPrimeSet B L τ C (coefficientPrimeSet B c)
    · rw [ite_eq_left hp]
      symm
      by_contra hw
      exact ha (candidateAdmissible_of_scalar hB hT hc hit hH hjT hw hp.1 hp.2)
    · rw [ite_eq_right hp]

end JointDickman

end OAI
