import OAI.NumberTheory.TwoPoint.Bounds.MultiplicativeExtraction
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.List.Prime

namespace OAI

/-! Exact decomposition along primes of a fixed dilation. The coefficient
of a smooth divisor is bounded by one; there is no signed local expansion
or factor exponential in the number of dilation primes. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def primeSmoothPart (P : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (fun p => p ∈ P)).prod

noncomputable def primeRoughPart (P : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (fun p => p ∉ P)).prod

lemma primeSmoothPart_mul_primeRoughPart (P : Finset ℕ) (n : ℕ) (hn : 0 < n) :
    primeSmoothPart P n * primeRoughPart P n = n := by
  have he := List.prod_map_filter_mul_prod_map_filter_not
    (fun p : ℕ => p ∈ P) (fun p : ℕ => p) n.primeFactorsList
  simpa [primeSmoothPart, primeRoughPart, Nat.prod_primeFactorsList hn.ne'] using he

lemma primeSmoothPart_pos (P : Finset ℕ) (n : ℕ) (hn : 0 < n) :
    0 < primeSmoothPart P n := by
  have he := primeSmoothPart_mul_primeRoughPart P n hn
  exact Nat.pos_of_ne_zero (fun hz => by rw [hz, zero_mul] at he; omega)

lemma primeRoughPart_pos (P : Finset ℕ) (n : ℕ) (hn : 0 < n) :
    0 < primeRoughPart P n := by
  have he := primeSmoothPart_mul_primeRoughPart P n hn
  exact Nat.pos_of_ne_zero (fun hz => by rw [hz, mul_zero] at he; omega)

lemma primeSmoothPart_support (P : Finset ℕ) (n : ℕ) :
    (primeSmoothPart P n).primeFactors ⊆ P := by
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨r, hr, hpr⟩ := hprime.prime.dvd_prod_iff.mp hd
  obtain ⟨hrn, hrP⟩ := List.mem_filter.mp hr
  have hrprime := Nat.prime_of_mem_primeFactorsList hrn
  have he : p = r := ((Nat.dvd_prime hrprime).mp hpr).resolve_left hprime.ne_one
  exact he.symm ▸ (of_decide_eq_true hrP)

lemma primeRoughPart_coprime (q n : ℕ) (hq : 0 < q) :
    q.Coprime (primeRoughPart q.primeFactors n) := by
  apply Nat.coprime_list_prod_right_iff.mpr
  intro p hp
  obtain ⟨hpn, hpq⟩ := List.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primeFactorsList hpn
  apply Nat.Coprime.symm
  apply hprime.coprime_iff_not_dvd.mpr
  intro hd
  exact (of_decide_eq_true hpq) (Nat.mem_primeFactors.mpr ⟨hprime, hd, hq.ne'⟩)

lemma coprime_of_primeFactors_subset {a q n : ℕ}
    (ha : 0 < a) (hs : a.primeFactors ⊆ q.primeFactors)
    (hqn : q.Coprime n) : a.Coprime n := by
  apply Nat.coprime_of_dvd'
  intro p hp hpa hpn
  have hpq := Nat.dvd_of_mem_primeFactors (hs (Nat.mem_primeFactors.mpr ⟨hp, hpa, ha.ne'⟩))
  have hcp : p.Coprime n := hqn.of_dvd_left hpq
  exact False.elim ((hp.coprime_iff_not_dvd.mp hcp) hpn)

lemma primeSmoothPart_unique (q n a : ℕ) (hq : 0 < q) (hn : 0 < n)
    (ha : a ∣ n) (hs : a.primeFactors ⊆ q.primeFactors) (hc : q.Coprime (n / a)) :
    a = primeSmoothPart q.primeFactors n := by
  have hap : 0 < a := Nat.pos_of_dvd_of_pos ha hn
  have hsp := primeSmoothPart_pos q.primeFactors n hn
  have he := primeSmoothPart_mul_primeRoughPart q.primeFactors n hn
  have har := coprime_of_primeFactors_subset hap hs (primeRoughPart_coprime q n hq)
  have has : a ∣ primeSmoothPart q.primeFactors n := by
    exact har.dvd_of_dvd_mul_right (he.symm ▸ ha)
  have hsc := coprime_of_primeFactors_subset hsp
    (primeSmoothPart_support q.primeFactors n) hc
  have hsa : primeSmoothPart q.primeFactors n ∣ a := by
    apply hsc.dvd_of_dvd_mul_right
    rw [Nat.mul_div_cancel' ha]
    exact ⟨primeRoughPart q.primeFactors n, he.symm⟩
  exact Nat.dvd_antisymm has hsa

noncomputable def coprimeRestriction (q : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if q.Coprime n then f n else 0

lemma coprimeRestriction_oneBounded (q : ℕ) {f : ℕ → ℂ} (hf : OneBounded f) :
    OneBounded (coprimeRestriction q f) := by
  intro n hn
  unfold coprimeRestriction
  split_ifs
  · exact hf n hn
  · simp

lemma coprimeRestriction_multiplicative (q : ℕ) {f : ℕ → ℂ}
    (hf : Multiplicative f) : Multiplicative (coprimeRestriction q f) := by
  intro a b ha hb hab
  unfold coprimeRestriction
  by_cases hqa : q.Coprime a
  · by_cases hqb : q.Coprime b
    · rw [ite_eq_left (Nat.coprime_mul_iff_right.mpr ⟨hqa, hqb⟩),
        ite_eq_left hqa, ite_eq_left hqb]
      exact hf a b ha hb hab
    · have hn : ¬q.Coprime (a * b) := fun hc => hqb (Nat.coprime_mul_iff_right.mp hc).2
      rw [ite_eq_right hn, ite_eq_left hqa, ite_eq_right hqb, mul_zero]
  · have hn : ¬q.Coprime (a * b) := fun hc => hqa (Nat.coprime_mul_iff_right.mp hc).1
    rw [ite_eq_right hn, ite_eq_right hqa, zero_mul]

lemma coprimeRestriction_prime (q : ℕ) (hq : 0 < q) (f : ℕ → ℂ)
    {p : ℕ} (hp : p.Prime) (hpq : p ∉ q.primeFactors) :
    coprimeRestriction q f p = f p := by
  apply ite_eq_left
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  exact hpq (Nat.mem_primeFactors.mpr ⟨hp, hd, hq.ne'⟩)

/-- The fixed-dilation sequence is a positive-density convolution over
smooth divisors; its scalar coefficients have modulus at most one. -/
theorem multiplicative_dilation_smooth_sum {f : ℕ → ℂ} (hf : Multiplicative f)
    (q n : ℕ) (hq : 0 < q) (hn : 0 < n) :
    f (q * n) = ∑ a ∈ n.divisors.filter (fun a => a.primeFactors ⊆ q.primeFactors),
      f (q * a) * coprimeRestriction q f (n / a) := by
  let s := primeSmoothPart q.primeFactors n
  let r := primeRoughPart q.primeFactors n
  have hs : 0 < s := primeSmoothPart_pos _ _ hn
  have hr : 0 < r := primeRoughPart_pos _ _ hn
  have he : s * r = n := primeSmoothPart_mul_primeRoughPart _ _ hn
  have hqr : q.Coprime r := primeRoughPart_coprime q n hq
  have hsr := coprime_of_primeFactors_subset hs (primeSmoothPart_support _ _) hqr
  have hdiv : s ∣ n := ⟨r, he.symm⟩
  have hmem : s ∈ n.divisors.filter (fun a => a.primeFactors ⊆ q.primeFactors) :=
    mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdiv, hn.ne'⟩, primeSmoothPart_support _ _⟩
  rw [sum_eq_single s]
  · rw [show n / s = r by rw [← he, Nat.mul_div_cancel_left _ hs]]
    rw [coprimeRestriction, ite_eq_left hqr, ← hf (q * s) r (Nat.mul_pos hq hs) hr
      (hqr.mul_left hsr)]
    congr 1
    rw [mul_assoc, he]
  · intro a ha hne
    unfold coprimeRestriction
    by_cases hc : q.Coprime (n / a)
    · have ha' := mem_filter.mp ha
      exact False.elim (hne (primeSmoothPart_unique q n a hq hn
        (Nat.mem_divisors.mp ha'.1).1 ha'.2 hc))
    · rw [ite_eq_right hc, mul_zero]
  · exact fun h => False.elim (h hmem)

end TwoPointCorrelations

end OAI
