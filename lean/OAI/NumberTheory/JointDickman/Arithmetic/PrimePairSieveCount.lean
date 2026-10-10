import OAI.NumberTheory.JointDickman.Arithmetic.PrimePairLocalSieve
import OAI.NumberTheory.JointDickman.Arithmetic.SieveInterval
import OAI.NumberTheory.JointDickman.Arithmetic.BrunUpperSieve
import OAI.NumberTheory.JointDickman.Arithmetic.MertensDischarge

namespace OAI

/-! # Applying the proved finite-event sieve to prime pairs -/
namespace JointDickman
open Finset

noncomputable def primePairCount (Q h : ℕ) : ℕ := by
  classical
  exact ((Ico 0 (Q+1)).filter (fun n => n.Prime ∧ (n+h).Prime)).card

/-- A finite cutoff bound with the exact pair density and a polynomial error.
The primes 2 and 3 are omitted so that every local density is at most 1/2. -/
theorem primePair_count_sieve_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Q Z h : ℕ, 3 ≤ Z → 0 < h →
      (primePairCount Q h:ℝ) ≤
        C*(Q+1:ℝ)*((h:ℝ)/h.totient)*
          (∏ p ∈ (Nat.primesLE Z).filter (fun p => 3 < p), (1-1/(p:ℝ)))^2 +
        2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ) := by
  classical
  obtain ⟨C,hC,hbound⟩ := weighted_interval_sieve_polynomial fordUpperSieveInput
    primeReciprocalMertensInput (k := 2) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro Q Z h hZ hh
  let P := (Nat.primesLE Z).filter (fun p => 3 < p)
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p ≤ Z ∧ 2*2 ≤ p := by
    obtain ⟨hps,hp3⟩ := mem_filter.mp hp
    obtain ⟨hpZ,hprime⟩ := Nat.mem_primesLE.mp hps
    exact ⟨hprime,hpZ,by omega⟩
  let A := fun p => primePairRoots p h
  let w := fun n => ∏ p ∈ rootEvents P A n, (0:ℝ)
  have hw (n : ℕ) : 0 ≤ w n := prod_nonneg (fun _ _ => le_rfl)
  have hsurvive (n : ℕ) (hn : n.Prime) (hnh : (n+h).Prime) (hZn : Z < n) :
      rootEvents P A n = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpP,hroot⟩ := mem_filter.mp hp
    have hprime := (hP p hpP).1
    have hpZ := (hP p hpP).2.1
    rcases (primePairRoots_mem p h n).mp hroot with hd | hd
    · have he := (Nat.prime_dvd_prime_iff_eq hprime hn).mp hd
      omega
    · have he := (Nat.prime_dvd_prime_iff_eq hprime hnh).mp hd
      omega
  have hpoint (n : ℕ) :
      (if n.Prime ∧ (n+h).Prime then (1:ℝ) else 0) ≤
        (if n ≤ Z then (1:ℝ) else 0)+w n := by
    by_cases hp : n.Prime ∧ (n+h).Prime
    · by_cases hnZ : n ≤ Z
      · simpa only [ite_eq_left hp,ite_eq_left hnZ] using le_add_of_nonneg_right (hw n)
      · have he := hsurvive n hp.1 hp.2 (by omega)
        simp [hp,hnZ,w,he]
    · simpa only [ite_eq_right hp] using add_nonneg (by split_ifs <;> norm_num) (hw n)
  have hsmall : (∑ n ∈ Ico 0 (Q+1), if n ≤ Z then (1:ℝ) else 0) ≤ (Z+1:ℝ) := by
    rw [sum_boole]
    have hs : (Ico 0 (Q+1)).filter (fun n => n ≤ Z) ⊆ Icc 0 Z := by
      intro n hn
      exact mem_Icc.mpr ⟨Nat.zero_le _,(mem_filter.mp hn).2⟩
    exact_mod_cast (show ((Ico 0 (Q+1)).filter (fun n => n ≤ Z)).card ≤ Z+1 by simpa using card_le_card hs)
  have hcount : (primePairCount Q h:ℝ) ≤ (Z+1:ℝ)+(∑ n ∈ Ico 0 (Q+1), w n) := by
    calc
      _ = ∑ n ∈ Ico 0 (Q+1), if n.Prime ∧ (n+h).Prime then (1:ℝ) else 0 := by
        simp [primePairCount]
      _ ≤ ∑ n ∈ Ico 0 (Q+1), ((if n ≤ Z then (1:ℝ) else 0)+w n) :=
        sum_le_sum (fun n _ => hpoint n)
      _ = (∑ n ∈ Ico 0 (Q+1), if n ≤ Z then (1:ℝ) else 0)+(∑ n ∈ Ico 0 (Q+1), w n) := sum_add_distrib
      _ ≤ _ := add_le_add hsmall le_rfl
  have hsieve := hbound P A (fun _ => 0) 0 (Q+1) Z (by omega) (by omega) hP
    (fun p _ => by simp [A,primePairRoots_card]; split_ifs <;> omega)
    (fun _ _ => by norm_num)
  simp only [Nat.cast_zero,sub_zero,mul_zero,add_zero] at hsieve
  have hdensity := primePair_local_product_bound (fun p hp => (hP p hp).1) hh
  have hmult := mul_le_mul_of_nonneg_left hdensity (show 0 ≤ C*(Q+1:ℝ) by positivity)
  change (∑ n ∈ Ico 0 (Q+1), w n) ≤ _ at hsieve
  dsimp only [A] at hsieve
  change (∏ p ∈ P, _) ≤ _ at hdensity
  push_cast at hsieve
  dsimp only [P] at hmult hsieve
  nlinarith

end JointDickman

end OAI
