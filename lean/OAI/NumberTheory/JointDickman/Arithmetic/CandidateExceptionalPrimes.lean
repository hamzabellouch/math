import OAI.NumberTheory.JointDickman.Amplification.CandidateRootGeometry
import OAI.NumberTheory.JointDickman.Arithmetic.LargeDivisorReciprocals

namespace OAI

/-! # Large-prime obstructions attached to actual candidate roots -/

namespace JointDickman
open Finset

noncomputable def candidateRootNumerator {M : ℕ} (e : BlockCandidateIndex M) : ℤ :=
  (candidateLow e : ℤ)-(e.1.1.val+1)*candidateQuotient e

noncomputable def candidateSiteValue {M : ℕ} (e : BlockCandidateIndex M) (s : Fin M) : ℤ :=
  (candidateLow e : ℤ)+((s.val : ℤ)-e.1.1.val)*candidateQuotient e

noncomputable def candidateRootDifference {M : ℕ} (e f : BlockCandidateIndex M) : ℤ :=
  candidateRootNumerator e*candidateQuotient f-candidateRootNumerator f*candidateQuotient e

theorem candidate_quotient_exp_bounds {B L T H M : ℕ} {τ C : ℝ}
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e) :
    Real.exp (B : ℝ) ≤ candidateQuotient e ∧
      (candidateQuotient e : ℝ) ≤ Real.exp (2*B) := by
  have hc : (0 : ℝ) < candidateQuotient e := by exact_mod_cast he.2.2.2.1
  have hlo := he.2.2.2.2.2.2.2.2.2.2.1
  have hhi := he.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨(Real.exp_le_exp.mpr hlo).trans_eq (Real.exp_log hc),
    (Real.exp_log hc).symm.trans_le (Real.exp_le_exp.mpr hhi)⟩

/-- An affine coefficient of a candidate has logarithmic size O(B), with
an explicit exponent sufficient for every exceptional-prime estimate. -/
theorem affine_candidate_size {B T M b c : ℕ} {t : ℤ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hc : (c : ℝ) ≤ Real.exp (2*B)) (hb : b ≤ 2*T*c) (ht : t.natAbs ≤ M) :
    (((b : ℤ)+t*c).natAbs : ℝ) ≤ Real.exp (5*B) := by
  have habs : ((b : ℤ)+t*c).natAbs ≤ b+t.natAbs*c := by
    simpa only [Int.natAbs_natCast,Int.natAbs_mul] using Int.natAbs_add_le (b : ℤ) (t*c)
  have ht' : (t.natAbs : ℝ) ≤ M := by exact_mod_cast ht
  have hb' : (b : ℝ) ≤ 2*T*c := by exact_mod_cast hb
  have hB' : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hbig : (3 : ℝ) ≤ Real.exp (2*B) := by
    have h := Real.add_one_le_exp (2*(B : ℝ))
    linarith
  calc
    (((b : ℤ)+t*c).natAbs : ℝ) ≤ (b : ℝ)+(t.natAbs : ℝ)*c := by exact_mod_cast habs
    _ ≤ (2*(T : ℝ)+M)*c := by nlinarith
    _ ≤ (3*Real.exp B)*Real.exp (2*B) :=
      mul_le_mul (by linarith) hc (Nat.cast_nonneg c) (by positivity)
    _ = 3*Real.exp (3*B) := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp (2*B)*Real.exp (3*B) := mul_le_mul_of_nonneg_right hbig (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem candidateRootNumerator_size {B L T H M : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e) :
    ((candidateRootNumerator e).natAbs : ℝ) ≤ Real.exp (5*B) := by
  have hi : e.1.1.val+1 ≤ M := by have h := e.1.1.isLt; omega
  have ht : (-(e.1.1.val+1 : ℤ)).natAbs ≤ M := by
    have hn : ((e.1.1.val : ℤ)+1) = ((e.1.1.val+1 : ℕ) : ℤ) := by push_cast; rfl
    rw [Int.natAbs_neg,hn,Int.natAbs_natCast]
    exact hi
  have hh := affine_candidate_size hB hT hM (candidate_quotient_exp_bounds he).2
    he.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ht
  simpa only [candidateRootNumerator,sub_eq_add_neg,neg_mul] using hh

theorem candidateSiteValue_size {B L T H M : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e) (s : Fin M) :
    ((candidateSiteValue e s).natAbs : ℝ) ≤ Real.exp (5*B) := by
  have ht : ((s.val : ℤ)-e.1.1.val).natAbs ≤ M := by
    have hh : |(s.val : ℤ)-e.1.1.val| ≤ (M : ℤ) := by
      apply abs_le.mpr
      have hs := s.isLt
      have hi := e.1.1.isLt
      constructor <;> omega
    rw [← Int.natCast_natAbs] at hh
    exact_mod_cast hh
  exact affine_candidate_size hB hT hM (candidate_quotient_exp_bounds he).2
    he.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ht

theorem candidateSiteValue_ne_zero {B L T H M : ℕ} {τ C : ℝ} (hB : 2 ≤ B)
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e) (s : Fin M) :
    candidateSiteValue e s ≠ 0 := by
  have hc : 1 < candidateQuotient e := by
    have h := (candidate_quotient_exp_bounds he).1
    have hb : (2 : ℝ) ≤ B := by exact_mod_cast hB
    have hx := Real.add_one_le_exp (B : ℝ)
    have : (1 : ℝ) < candidateQuotient e := by linarith
    exact_mod_cast this
  exact translated_candidate_coefficient_ne_zero he.2.2.2.2.2.2.1 hc _

/-- Forced hits at another endpoint involve only primes dividing this
nonzero affine coefficient. -/
theorem candidateSiteValue_prime_mass {B L T H M : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e) (s : Fin M)
    (P : ℝ) (hP : 0 < P) (Q : Finset ℕ)
    (hQ : Q ⊆ (candidateSiteValue e s).natAbs.primeFactors)
    (hcut : ∀ p ∈ Q, P ≤ (p : ℝ)) :
    (∑ p ∈ Q, 1/(p : ℝ)) ≤ (5*(B : ℝ))/(Real.log 2*P) :=
  large_prime_divisor_reciprocals (candidateSiteValue_ne_zero hB he s) Q hQ hP hcut
    (candidateSiteValue_size hB hT hM he s)


theorem candidateRoot_fraction {B L T H M : ℕ} {τ C : ℝ}
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e) :
    blockCandidateRoot e = (candidateRootNumerator e : ℚ)/(candidateQuotient e : ℚ) := by
  exact shiftedCandidateRoot_fraction _ _ _ he.2.2.2.1.ne'

theorem candidateRootDifference_ne_zero {B L T H M : ℕ} {τ C : ℝ}
    {e f : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e)
    (hf : BlockCandidateAdmissible B L T H τ C f)
    (hroots : blockCandidateRoot e ≠ blockCandidateRoot f) :
    candidateRootDifference e f ≠ 0 := by
  intro hzero
  apply hroots
  rw [candidateRoot_fraction he,candidateRoot_fraction hf]
  have he0 : (candidateQuotient e : ℚ) ≠ 0 := by exact_mod_cast he.2.2.2.1.ne'
  have hf0 : (candidateQuotient f : ℚ) ≠ 0 := by exact_mod_cast hf.2.2.2.1.ne'
  apply (div_eq_div_iff he0 hf0).mpr
  unfold candidateRootDifference at hzero
  have hz := sub_eq_zero.mp hzero
  exact_mod_cast hz

theorem candidateRootDifference_size {B L T H M : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    {e f : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e)
    (hf : BlockCandidateAdmissible B L T H τ C f) :
    ((candidateRootDifference e f).natAbs : ℝ) ≤ Real.exp (8*B) := by
  have hne := candidateRootNumerator_size hB hT hM he
  have hnf := candidateRootNumerator_size hB hT hM hf
  have hce := (candidate_quotient_exp_bounds he).2
  have hcf := (candidate_quotient_exp_bounds hf).2
  have hn : (candidateRootDifference e f).natAbs ≤
      (candidateRootNumerator e).natAbs*candidateQuotient f+
        (candidateRootNumerator f).natAbs*candidateQuotient e := by
    simpa only [candidateRootDifference,sub_eq_add_neg,Int.natAbs_neg,Int.natAbs_mul,
      Int.natAbs_natCast] using Int.natAbs_add_le
      (candidateRootNumerator e*candidateQuotient f)
      (-(candidateRootNumerator f*candidateQuotient e))
  have hB' : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hexp2 : (2 : ℝ) ≤ Real.exp B := by
    have h := Real.add_one_le_exp (B : ℝ)
    linarith
  calc
    ((candidateRootDifference e f).natAbs : ℝ) ≤
        ((candidateRootNumerator e).natAbs : ℝ)*candidateQuotient f+
        ((candidateRootNumerator f).natAbs : ℝ)*candidateQuotient e := by exact_mod_cast hn
    _ ≤ Real.exp (5*B)*Real.exp (2*B)+Real.exp (5*B)*Real.exp (2*B) :=
      add_le_add (mul_le_mul hne hcf (Nat.cast_nonneg _) (Real.exp_pos _).le)
        (mul_le_mul hnf hce (Nat.cast_nonneg _) (Real.exp_pos _).le)
    _ = 2*Real.exp (7*B) := by
      have hh : (5 : ℝ)*B+2*B = 7*B := by ring
      rw [← Real.exp_add,hh]
      ring
    _ ≤ Real.exp B*Real.exp (7*B) := mul_le_mul_of_nonneg_right hexp2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Distinct rational roots can collide modulo primes only at a set whose
reciprocal mass has this uniform bound. -/
theorem candidateRootDifference_prime_mass {B L T H M : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    {e f : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e)
    (hf : BlockCandidateAdmissible B L T H τ C f)
    (hroots : blockCandidateRoot e ≠ blockCandidateRoot f)
    (P : ℝ) (hP : 0 < P) (Q : Finset ℕ)
    (hQ : Q ⊆ (candidateRootDifference e f).natAbs.primeFactors)
    (hcut : ∀ p ∈ Q, P ≤ (p : ℝ)) :
    (∑ p ∈ Q, 1/(p : ℝ)) ≤ (8*(B : ℝ))/(Real.log 2*P) :=
  large_prime_divisor_reciprocals (candidateRootDifference_ne_zero he hf hroots)
    Q hQ hP hcut (candidateRootDifference_size hB hT hM he hf)

end JointDickman

end OAI
