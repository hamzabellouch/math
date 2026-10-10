import OAI.NumberTheory.JointDickman.Arithmetic.BrunUpperSieve
import OAI.NumberTheory.JointDickman.Arithmetic.MertensDischarge
import OAI.NumberTheory.JointDickman.Arithmetic.SieveRemainders
import OAI.NumberTheory.JointDickman.Arithmetic.SieveDimension

namespace OAI

/-! # The proved sieve applied to nonnegative Mellin square weights -/
namespace JointDickman
open Finset
open scoped Classical

lemma sieve_level_card_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Z : ℕ) :
    (P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ Z)).card ≤ Z+1 := by
  rw [← card_range (Z+1)]
  apply card_le_card_of_injOn (fun D => ∏ p ∈ D, p)
  · intro D hD
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hD).2)
  · intro D hD E hE hDE
    exact primeProduct_injective hP (mem_powerset.mp (mem_filter.mp hD).1)
      (mem_powerset.mp (mem_filter.mp hE).1) hDE

noncomputable def primeDivisorEvents (P : Finset ℕ) (n : ℕ) : Finset ℕ :=
  P.filter (fun p => p ∣ n)

lemma primeDivisorEvents_prime {P : Finset ℕ} {Z n : ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Z) (hn : n.Prime) (hZn : Z < n) :
    primeDivisorEvents P n = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hpP, hpn⟩ := mem_filter.mp hp
  have he := (Nat.prime_dvd_prime_iff_eq (hP p hpP).1 hn).mp hpn
  have := (hP p hpP).2
  omega

/-- Positive weights on primes larger than the sieve level. The error is
the literal sum of residue-class discrepancies of the given weight. -/
theorem prime_weighted_sieve : ∃ C : ℝ, 0 < C ∧
    ∀ (K Z : ℕ) (P Q : Finset ℕ) (w : ℕ → ℝ) (M R : ℝ),
      2 ≤ Z → 0 ≤ M → 0 ≤ R →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z) →
      Q ⊆ Icc 1 K → (∀ q ∈ Q, q.Prime ∧ Z < q) →
      (∀ n ∈ Icc 1 K, 0 ≤ w n) →
      (∀ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ Z),
        |sieveRemainder (fun n : Icc 1 K => primeDivisorEvents P n)
          (fun n => w n) M (fun p => 1/(p : ℝ)) D| ≤ R) →
      (∑ q ∈ Q, w q) ≤ C*M*(∏ p ∈ P, (1-1/(p : ℝ))) + (Z+1:ℕ)*R := by
  obtain ⟨A, hA, hdim⟩ := sieveDimension_of_reciprocal_bound primeReciprocalMertensInput
    (k := 1) (by norm_num)
  obtain ⟨C, hC, hbound⟩ := fordUpperSieveInput 2 A (by norm_num) hA
  refine ⟨C, hC, ?_⟩
  intro K Z P Q w M R hZ hM hR hP hQ hQprime hw herr
  have hg : ∀ p ∈ P, 0 ≤ 1/(p : ℝ) ∧ 1/(p : ℝ) ≤ 1/2 ∧
      1/(p : ℝ) ≤ 1/(p : ℝ) := by
    intro p hp
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (hP p hp).1.two_le
    exact ⟨by positivity, one_div_le_one_div_of_le (by norm_num) hp2, le_rfl⟩
  have hs := hbound (Icc 1 K) P (fun n => primeDivisorEvents P n)
    (fun n => w n) M Z (fun p => 1/(p : ℝ)) (by exact_mod_cast hZ) hM
    (fun n => hw n n.property)
    (fun p hp => ⟨(hP p hp).1, by exact_mod_cast (hP p hp).2⟩)
    (fun p hp => ⟨(hg p hp).1, lt_of_le_of_lt (hg p hp).2.1 (by norm_num)⟩)
    (by simpa only [mul_one] using hdim P _ Z (fun p hp => (hP p hp).1) hg)
  simp only [Nat.cast_le] at hs
  have havoid (q : ℕ) (hq : q ∈ Q) : avoidsSelected P (primeDivisorEvents P q) = 1 := by
    rw [primeDivisorEvents_prime hP (hQprime q hq).1 (hQprime q hq).2]
    simp [avoidsSelected]
  have hleft : (∑ q ∈ Q, w q) ≤
      ∑ n : Icc 1 K, w n*avoidsSelected P (primeDivisorEvents P n) := by
    rw [(Icc 1 K).sum_coe_sort (fun n : ℕ => w n*avoidsSelected P (primeDivisorEvents P n))]
    calc
      _ = ∑ q ∈ Q, w q*avoidsSelected P (primeDivisorEvents P q) := by
        apply sum_congr rfl
        intro q hq
        rw [havoid q hq, mul_one]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hQ (by
        intro n hn _
        exact mul_nonneg (hw n hn) (by unfold avoidsSelected; split_ifs <;> norm_num))
  apply hleft.trans (hs.trans _)
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ Z), R :=
      sum_le_sum herr
    _ = ((P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ Z)).card : ℝ)*R := by simp
    _ ≤ _ := by
      have hh : ((P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ Z)).card : ℝ) ≤ (Z+1 : ℕ) := by
        exact_mod_cast sieve_level_card_le P (fun p hp => (hP p hp).1) Z
      exact mul_le_mul_of_nonneg_right hh hR

end JointDickman

end OAI
