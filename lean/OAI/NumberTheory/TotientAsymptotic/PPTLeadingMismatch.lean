import OAI.NumberTheory.TotientAsymptotic.PPTPreimageEquation

namespace OAI

/-!
Transport the actual largest-prime mismatch into the ordered high-prime
list used in the comparison equation.  Retaining the canonical low part
is essential here: smoothness of its totient alone would not suffice.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma ppt_largestPrimeFactor_mono_dvd {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) :
    largestPrimeFactor a ≤ largestPrimeFactor b := by
  apply largestPrimeFactor_le_of_prime_divisors (le_max_left _ _)
  intro r hr hra _
  exact prime_dvd_le_largest hr hb.ne' (hra.trans hab)

/-- A normal shifted prime dividing the target forces an actual prime
above the low cutoff as soon as its interval has positive normality
mass. -/
lemma ppt_preimage_largest_above_normal_shift {n r : ℕ} {S T : ℝ}
    (hn : 0 < n) (hr : IsNormalPrime S r) (hdiv : r-1 ∣ n.totient)
    (hST : S < T) (hTr : T ≤ (r-1 : ℕ))
    (hgap : Real.sqrt (B S*B T) < B T-B S) :
    S < (largestPrimeFactor n : ℝ) := by
  by_contra hh
  have hnsmall : (largestPrimeFactor n : ℝ) ≤ S := le_of_not_gt hh
  have hshift : (largestPrimeFactor (r-1) : ℝ) ≤ S := by
    exact (Nat.cast_le.mpr ((ppt_largestPrimeFactor_mono_dvd
      (Nat.totient_pos.mpr hn) hdiv).trans (largestPrimeFactor_totient_le n))).trans hnsmall
  have hz := omegaIn_eq_zero_of_largest_le (T := T) hshift
  have hb := (normality_interval_bounds hr le_rfl hST hTr le_rfl).1
  rw [hz, Nat.cast_zero] at hb
  linarith

lemma ppt_actual_preimage_largest_above_of_gap {k d n : ℕ} (p : Fin k → ℕ)
    (j : Fin k) {S T : ℝ} (hn : 0 < n)
    (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p)
    (hvalue : n.totient = d*(∏ i, p i).totient)
    (hj : IsNormalPrime S (p j)) (hST : S < T) (hTj : T ≤ (p j-1 : ℕ))
    (hgap : Real.sqrt (B S*B T) < B T-B S) :
    S < (largestPrimeFactor n : ℝ) := by
  have hdiv : p j-1 ∣ n.totient := by
    rw [hvalue, ppt_totient_primeProduct p hp hpinj]
    exact (Finset.dvd_prod_of_mem (fun i => p i-1) (Finset.mem_univ j)).trans
      (dvd_mul_left _ _)
  exact ppt_preimage_largest_above_normal_shift hn hj hdiv hST hTj hgap

lemma ppt_partBelow_largest_le (n : ℕ) {S : ℝ} (hS : 1 ≤ S) :
    (largestPrimeFactor (partBelow n S) : ℝ) ≤ S := by
  have hn : largestPrimeFactor (partBelow n S) ≤ ⌊S⌋₊ := by
    apply largestPrimeFactor_le_of_prime_divisors
      (Nat.le_floor (by simpa only [Nat.cast_one] using hS))
    intro p hp hpn _
    exact Nat.le_floor (ppt_partBelow_prime_le hp hpn)
  exact (Nat.cast_le.mpr hn).trans (Nat.floor_le (zero_le_one.trans hS))

lemma ppt_leading_prime_of_split {l n s : ℕ} (hl : 0 < l) (q : Fin l → ℕ)
    {S : ℝ} (hs : 0 < s) (hreal : n = s*∏ i, q i)
    (hsmall : (largestPrimeFactor s : ℝ) ≤ S)
    (hprime : ∀ i, (q i).Prime) (hanti : StrictAnti q)
    (hhigh : S < (q ⟨0, hl⟩ : ℝ)) :
    largestPrimeFactor n = q ⟨0, hl⟩ := by
  have hqpos : 0 < ∏ i, q i := Finset.prod_pos (fun i _ => (hprime i).pos)
  have hn : n ≠ 0 := by rw [hreal]; exact (Nat.mul_pos hs hqpos).ne'
  have hqbound (i : Fin l) : q i ≤ q ⟨0, hl⟩ :=
    hanti.antitone (show (⟨0, hl⟩ : Fin l) ≤ i from Nat.zero_le i.val)
  have hslow : largestPrimeFactor s ≤ q ⟨0, hl⟩ := by
    exact_mod_cast hsmall.trans hhigh.le
  apply le_antisymm
  · rw [hreal]
    apply largestPrimeFactor_mul_le hslow
    apply largestPrimeFactor_prod_le _ _ (hprime ⟨0, hl⟩).one_lt.le
    intro i _
    rw [largestPrimeFactor_prime (hprime i)]
    exact hqbound i
  · apply prime_dvd_le_largest (hprime ⟨0, hl⟩) hn
    rw [hreal]
    exact (Finset.dvd_prod_of_mem q (Finset.mem_univ ⟨0, hl⟩)).trans
      (dvd_mul_left _ _)

/-- An actual preimage with a prime above `S` has a nonempty high list,
and its first entry is its largest prime. -/
theorem ppt_preimage_split_largest {n : ℕ} {S : ℝ} (hn : 0 < n) (hS : 1 ≤ S)
    (hsq : SquarefreeAbove n S)
    (hnormal : ∀ p : ℕ, p.Prime → p ∣ n → IsNormalPrime S p)
    (hlarge : S < (largestPrimeFactor n : ℝ)) :
    ∃ (l : ℕ) (hl : 0 < l) (q : Fin l → ℕ) (s : ℕ),
      0 < s ∧ n = s*∏ i, q i ∧
      (largestPrimeFactor s.totient : ℝ) ≤ S ∧ StrictAnti q ∧
      (∀ i, IsNormalPrime S (q i) ∧ S < (q i : ℝ)) ∧
      n.totient = s.totient*shiftedProduct q ∧
      largestPrimeFactor n = q ⟨0, hl⟩ := by
  obtain ⟨l, q, s, hs, hreal, _, hsmall, hanti, hq, hφ, hslow⟩ :=
    ppt_preimage_prime_split_full hn hS hsq hnormal
  have hsmooth : (largestPrimeFactor s : ℝ) ≤ S := by
    rw [hslow]
    exact ppt_partBelow_largest_le n hS
  have hl : 0 < l := by
    by_contra hh
    have hl0 : l = 0 := Nat.eq_zero_of_not_pos hh
    have hprod : (∏ i, q i) = 1 := by subst l; simp
    have hns : n = s := by simpa only [hprod, mul_one] using hreal
    exact (not_lt_of_ge (hns.symm ▸ hsmooth)) hlarge
  refine ⟨l, hl, q, s, hs, hreal, hsmall, hanti, hq, hφ, ?_⟩
  exact ppt_leading_prime_of_split hl q hs hreal hsmooth
    (fun i => (hq i).1.1) hanti (hq ⟨0, hl⟩).2

/-- The mismatch supplied by the maximal common-prefix argument now
holds for the first displayed high prime in the literal comparison
equation, rather than being an additional assumption about that list. -/
theorem ppt_actual_preimage_leading_mismatch {k d n r : ℕ} (p : Fin k → ℕ)
    {S : ℝ} (hn : 0 < n) (hS : 1 ≤ S)
    (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p)
    (hvalue : n.totient = d*(∏ i, p i).totient)
    (hsq : SquarefreeAbove n S)
    (hnormal : ∀ q : ℕ, q.Prime → q ∣ n → IsNormalPrime S q)
    (hlarge : S < (largestPrimeFactor n : ℝ))
    (hmismatch : largestPrimeFactor n ≠ r) :
    ∃ (l : ℕ) (hl : 0 < l) (q : Fin l → ℕ) (E : ℕ),
      0 < E ∧ (largestPrimeFactor E : ℝ) ≤ S ∧ StrictAnti q ∧
      (∀ i, IsNormalPrime S (q i) ∧ S < (q i : ℝ)) ∧
      d*shiftedProduct p = E*shiftedProduct q ∧ q ⟨0, hl⟩ ≠ r := by
  obtain ⟨l, hl, q, s, hs, _, hsmall, hanti, hq, hφ, hlead⟩ :=
    ppt_preimage_split_largest hn hS hsq hnormal hlarge
  refine ⟨l, hl, q, s.totient, Nat.totient_pos.mpr hs, hsmall, hanti, hq, ?_, ?_⟩
  · calc
      d*shiftedProduct p = d*(∏ i, p i).totient := by
        rw [ppt_totient_primeProduct p hp hpinj]
      _ = n.totient := hvalue.symm
      _ = s.totient*shiftedProduct q := hφ
  · exact hlead ▸ hmismatch

/-- Version with the high-prime existence derived from the concrete
normality gap on one candidate shift. -/
theorem ppt_actual_preimage_leading_mismatch_of_gap {k d n r : ℕ}
    (p : Fin k → ℕ) (j : Fin k) {S T : ℝ} (hn : 0 < n) (hS : 1 ≤ S)
    (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p)
    (hvalue : n.totient = d*(∏ i, p i).totient)
    (hsq : SquarefreeAbove n S)
    (hnormal : ∀ q : ℕ, q.Prime → q ∣ n → IsNormalPrime S q)
    (hj : IsNormalPrime S (p j)) (hST : S < T) (hTj : T ≤ (p j-1 : ℕ))
    (hgap : Real.sqrt (B S*B T) < B T-B S)
    (hmismatch : largestPrimeFactor n ≠ r) :
    ∃ (l : ℕ) (hl : 0 < l) (q : Fin l → ℕ) (E : ℕ),
      0 < E ∧ (largestPrimeFactor E : ℝ) ≤ S ∧ StrictAnti q ∧
      (∀ i, IsNormalPrime S (q i) ∧ S < (q i : ℝ)) ∧
      d*shiftedProduct p = E*shiftedProduct q ∧ q ⟨0, hl⟩ ≠ r := by
  exact ppt_actual_preimage_leading_mismatch p hn hS hp hpinj hvalue hsq hnormal
    (ppt_actual_preimage_largest_above_of_gap p j hn hp hpinj hvalue hj hST hTj hgap)
    hmismatch

end TotientAsymptotic

end

end OAI
