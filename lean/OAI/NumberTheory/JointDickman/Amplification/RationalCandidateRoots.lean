import OAI.NumberTheory.JointDickman.Counting.BlockCandidates
import Mathlib.Data.Rat.Lemmas

namespace OAI

/-! # Rational roots of candidate representations -/

namespace JointDickman

noncomputable def shiftedCandidateRoot (b c : ℕ) (i : ℤ) : ℚ := (b : ℚ)/c-i

theorem shifted_numerator_coprime {b c : ℕ} (hbc : b.Coprime c) (i : ℤ) :
    ((b : ℤ)-i*c).natAbs.Coprime c := by
  change Int.gcd ((b : ℤ)-i*c) (c : ℤ) = 1
  rw [Int.gcd_sub_mul_right_left]
  simpa only [Int.gcd,Int.natAbs_natCast] using hbc

theorem shiftedCandidateRoot_fraction (b c : ℕ) (i : ℤ) (hc : c ≠ 0) :
    shiftedCandidateRoot b c i = (((b : ℤ)-i*c : ℤ) : ℚ)/(c : ℚ) := by
  unfold shiftedCandidateRoot
  push_cast
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  field_simp

/-- Equal rational roots force equal reduced denominators and prescribe
exactly the coefficient at any other position. -/
theorem shiftedCandidateRoot_injective {b c b' c' : ℕ} {i i' : ℤ}
    (hc : 0 < c) (hc' : 0 < c') (hbc : b.Coprime c) (hbc' : b'.Coprime c')
    (he : shiftedCandidateRoot b c i = shiftedCandidateRoot b' c' i') :
    c = c' ∧ (b' : ℤ) = b+(i'-i)*c := by
  rw [shiftedCandidateRoot_fraction b c i hc.ne',
    shiftedCandidateRoot_fraction b' c' i' hc'.ne'] at he
  have hr := Rat.div_int_inj (by exact_mod_cast hc : (0 : ℤ) < c)
    (by exact_mod_cast hc' : (0 : ℤ) < c')
    (by simpa only [Int.natAbs_natCast] using shifted_numerator_coprime hbc i)
    (by simpa only [Int.natAbs_natCast] using shifted_numerator_coprime hbc' i') he
  have hcc : c = c' := by exact_mod_cast hr.2
  refine ⟨hcc, ?_⟩
  subst c'
  linear_combination -hr.1

/-- A reduced coefficient with denominator greater than one can never
vanish after translation by an integer multiple of that denominator. -/
theorem translated_candidate_coefficient_ne_zero {b c : ℕ}
    (hbc : b.Coprime c) (hc : 1 < c) (t : ℤ) : (b : ℤ)+t*c ≠ 0 := by
  intro he
  have hg : Int.gcd ((b : ℤ)+t*c) (c : ℤ) = 1 := by
    rw [Int.gcd_add_mul_right_left]
    simpa only [Int.gcd,Int.natAbs_natCast] using hbc
  rw [he,Int.zero_gcd,Int.natAbs_natCast] at hg
  omega

end JointDickman

end OAI
