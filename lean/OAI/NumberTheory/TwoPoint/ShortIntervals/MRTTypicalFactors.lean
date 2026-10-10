import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRamareIdentity
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTEulerProducts
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-! Exact finite typical-factorization masks used by MRT.  The prime bands
are kept arbitrary here; scale and sieve bounds are separate analytic steps. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical BigOperators

def mrtPrimeAvoids (P : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ P, ¬ p ∣ n

noncomputable def mrtPrimeMask (P : Finset ℕ) (n : ℕ) : ℝ :=
  if mrtPrimeAvoids P n then 1 else 0

def mrtTypical {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ) (n : ℕ) : Prop :=
  ∀ j ∈ J, ∃ p ∈ P j, p ∣ n

lemma mrtPrimeMask_bounds (P : Finset ℕ) (n : ℕ) :
    0 ≤ mrtPrimeMask P n ∧ mrtPrimeMask P n ≤ 1 := by
  unfold mrtPrimeMask
  split_ifs <;> norm_num

lemma mrtPrimeAvoids_union (P Q : Finset ℕ) (n : ℕ) :
    mrtPrimeAvoids (P ∪ Q) n ↔ mrtPrimeAvoids P n ∧ mrtPrimeAvoids Q n := by
  simp only [mrtPrimeAvoids, mem_union]
  aesop

lemma mrtPrimeMask_union (P Q : Finset ℕ) (n : ℕ) :
    mrtPrimeMask (P ∪ Q) n = mrtPrimeMask P n * mrtPrimeMask Q n := by
  simp only [mrtPrimeMask, mrtPrimeAvoids_union]
  by_cases hp : mrtPrimeAvoids P n <;> by_cases hq : mrtPrimeAvoids Q n <;> simp [hp, hq]

lemma mrtPrimeAvoids_mul (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m n : ℕ) :
    mrtPrimeAvoids P (m * n) ↔ mrtPrimeAvoids P m ∧ mrtPrimeAvoids P n := by
  simp only [mrtPrimeAvoids]
  constructor
  · intro h
    exact ⟨fun p hp hpm => h p hp (dvd_mul_of_dvd_left hpm n),
      fun p hp hpn => h p hp (dvd_mul_of_dvd_right hpn m)⟩
  · rintro ⟨hm, hn⟩ p hp hdiv
    exact ((hP p hp).dvd_mul.mp hdiv).elim (hm p hp) (hn p hp)

lemma mrtPrimeMask_mul (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m n : ℕ) :
    mrtPrimeMask P (m * n) = mrtPrimeMask P m * mrtPrimeMask P n := by
  simp only [mrtPrimeMask, mrtPrimeAvoids_mul P hP]
  by_cases hm : mrtPrimeAvoids P m <;> by_cases hn : mrtPrimeAvoids P n <;> simp [hm, hn]

lemma mrtPrimeMask_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    mrtPrimeMask P 1 = 1 := by
  unfold mrtPrimeMask
  apply ite_eq_left
  intro p hp hdiv
  exact (hP p hp).ne_one (Nat.eq_one_of_dvd_one hdiv)

lemma mrtPrimeMask_prime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {p : ℕ} (hp : p.Prime) : mrtPrimeMask P p = if p ∈ P then 0 else 1 := by
  have he : mrtPrimeAvoids P p ↔ p ∉ P := by
    constructor
    · intro h hmem
      exact h p hmem (dvd_refl p)
    · intro h q hq hqp
      have heq : q = p := (Nat.prime_dvd_prime_iff_eq (hP q hq) hp).mp hqp
      exact h (heq ▸ hq)
  simp only [mrtPrimeMask, he]
  split_ifs <;> simp_all

lemma mrtPrimeMask_biUnion {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ) (n : ℕ) :
    mrtPrimeMask (J.biUnion P) n = ∏ j ∈ J, mrtPrimeMask (P j) n := by
  induction J using Finset.induction_on with
  | empty => simp [mrtPrimeMask, mrtPrimeAvoids]
  | @insert j J hj ih =>
    rw [biUnion_insert, mrtPrimeMask_union, prod_insert hj, ih]

lemma mrtTypical_prod {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ) (n : ℕ) :
    (∏ j ∈ J, (1 - mrtPrimeMask (P j) n)) = if mrtTypical J P n then 1 else 0 := by
  induction J using Finset.induction_on with
  | empty => simp [mrtTypical]
  | @insert j J hj ih =>
    rw [prod_insert hj, ih]
    have he : mrtTypical (insert j J) P n ↔
        (¬ mrtPrimeAvoids (P j) n) ∧ mrtTypical J P n := by
      simp only [mrtTypical, mem_insert, mrtPrimeAvoids]
      push Not
      aesop
    rw [he]
    by_cases ha : mrtPrimeAvoids (P j) n <;> by_cases ht : mrtTypical J P n <;>
      simp [mrtPrimeMask, ha, ht]

/-- Exact inclusion-exclusion over missing prime bands, the expansion in
MRT Appendix A before its near-twist mean-value estimate. -/
theorem mrtTypical_inclusion_exclusion {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (n : ℕ) :
    (∑ I ∈ J.powerset, (-1 : ℝ) ^ I.card * mrtPrimeMask (I.biUnion P) n) =
      if mrtTypical J P n then 1 else 0 := by
  rw [← mrtTypical_prod, prod_sub]
  apply sum_congr rfl
  intro I _
  rw [prod_const_one, mul_one, mrtPrimeMask_biUnion]

lemma mrtPrimeAvoids_of_lt (P : Finset ℕ) {d : ℕ} (hd : 0 < d)
    (hP : ∀ p ∈ P, d < p) : mrtPrimeAvoids P d := by
  intro p hp hpd
  exact (not_le_of_gt (hP p hp)) (Nat.le_of_dvd hd hpd)

/-- Dividing out a number smaller than all the selected primes does not
change membership in the typical-factorization set. -/
theorem mrtTypical_mul_of_avoids {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime) {d : ℕ}
    (hd : mrtPrimeAvoids (J.biUnion P) d) (n : ℕ) :
    mrtTypical J P (d * n) ↔ mrtTypical J P n := by
  constructor
  · intro h j hj
    obtain ⟨p, hp, hpdn⟩ := h j hj
    refine ⟨p, hp, ?_⟩
    exact ((hP j hj p hp).dvd_mul.mp hpdn).resolve_left
      (hd p (mem_biUnion.mpr ⟨j, hj, hp⟩))
  · intro h j hj
    obtain ⟨p, hp, hpn⟩ := h j hj
    exact ⟨p, hp, dvd_mul_of_dvd_right hpn d⟩

lemma mrtPrimeMask_complex_oneBounded (P : Finset ℕ) :
    OneBounded (fun n => (mrtPrimeMask P n : ℂ)) := by
  intro n _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mrtPrimeMask_bounds P n).1]
  exact (mrtPrimeMask_bounds P n).2

lemma mrtPrimeMask_complex_multiplicative (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Multiplicative (fun n => (mrtPrimeMask P n : ℂ)) := by
  intro m n _ _ _
  simp only [mrtPrimeMask_mul P hP, Complex.ofReal_mul]

end TwoPointCorrelations

end OAI
