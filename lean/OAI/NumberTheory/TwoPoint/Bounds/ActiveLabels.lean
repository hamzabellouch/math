import OAI.NumberTheory.TwoPoint.Walks.ReversedSegments

namespace OAI

/-! Active numerical labels in minimal prohibited witnesses. -/

namespace TwoPointCorrelations

open Finset

noncomputable def wordPrimeContribution (h : ℕ) (w : List SignedStep) (p a b : ℕ) : ℤ := by
  classical
  exact ∑ i ∈ Ico a b, if TuplePrimeAt w p i then wordStepDisplacement h w i else 0

/-- A contiguous relation with a nonzero contribution from this label. -/
def ActivePrime (h : ℕ) (w : List SignedStep) (p : ℕ) : Prop :=
  ∃ c a b, a ≤ b ∧ b ≤ w.length ∧ (∃ i, TuplePrimeAt w c i) ∧
    (c : ℤ) ∣ intervalDisplacement (wordStepDisplacement h w) a b ∧
    ¬(c : ℤ) ∣ wordPrimeContribution h w p a b

lemma wordPrimeContribution_eq_interval (h : ℕ) (w : List SignedStep) (p a b : ℕ)
    (hp : ∀ i ∈ Ico a b, TuplePrimeAt w p i) :
    wordPrimeContribution h w p a b = intervalDisplacement (wordStepDisplacement h w) a b := by
  classical
  unfold wordPrimeContribution intervalDisplacement
  apply sum_congr rfl
  intro i hi
  simp only [hp i hi, ite_true]

lemma wordPrimeContribution_eq_singleton (h : ℕ) (w : List SignedStep) (p a b j : ℕ)
    (hj : j ∈ Ico a b) (hp : TuplePrimeAt w p j)
    (hunique : ∀ i ∈ Ico a b, TuplePrimeAt w p i → i = j) :
    wordPrimeContribution h w p a b = wordStepDisplacement h w j := by
  classical
  unfold wordPrimeContribution
  rw [sum_eq_single j]
  · simp only [hp, ite_true]
  · intro i hi hne
    have hnot : ¬TuplePrimeAt w p i := fun hpi => hne (hunique i hi hpi)
    simp only [hnot, ite_false]
  · exact fun h => False.elim (h hj)

/-- A label first entering at the last step is active in the original
prohibited suffix, because its contribution is exactly that last step. -/
lemma ForwardProhibited.last_new_active {h s : ℕ} {supply : ℕ → ℕ → Prop}
    {w : List SignedStep} (hw : ForwardProhibited h s supply w) {z : ℕ}
    (hz : TuplePrimeAt w z (w.length - 1))
    (hearlier : ∀ i, i < w.length - 1 → ¬TuplePrimeAt w z i)
    (hoff : ∀ p i, (∃ j, TuplePrimeAt w p j) → i < w.length →
      ¬TuplePrimeAt w p i → ¬(p : ℤ) ∣ wordStepDisplacement h w i) :
    ActivePrime h w z := by
  rcases hw with ⟨hlen, _, _, _, _, c, hc, hclast, a, ha, halast, hdiv⟩
  refine ⟨c, a, w.length, by omega, le_rfl, ⟨0, hc⟩, ?_, ?_⟩
  · simpa only [wordSlice, Nat.sub_self, List.take_length, List.length_drop] using
      (show (c : ℤ) ∣ intervalDisplacement (wordStepDisplacement h w) a w.length from by
        rw [← wordSlice_displacement h w (by omega)]
        simpa only [wordSlice, ← List.length_drop, List.take_length] using hdiv)
  · rw [wordPrimeContribution_eq_singleton h w z a w.length (w.length - 1)
      (by simp only [mem_Ico]; omega) hz]
    · exact hoff c (w.length - 1) ⟨0, hc⟩ (by omega) hclast
    · intro i hi hzi
      have hi' := (mem_Ico.mp hi).2
      by_contra hne
      exact hearlier i (by omega) hzi

lemma prime_dvd_wordPrimeContribution (h : ℕ) (w : List SignedStep) (p a b : ℕ) :
    (p : ℤ) ∣ wordPrimeContribution h w p a b := by
  classical
  unfold wordPrimeContribution
  apply Finset.dvd_sum
  intro i _
  by_cases hpi : TuplePrimeAt w p i
  · simpa only [hpi, ite_true] using (tuplePrime_dvd_step (h := h) hpi)
  · simp only [hpi, ite_false, dvd_zero]

lemma ActivePrime.distinct_controller {h p : ℕ} {w : List SignedStep}
    (hp : ActivePrime h w p) :
    ∃ c a b, c ≠ p ∧ a ≤ b ∧ b ≤ w.length ∧ (∃ i, TuplePrimeAt w c i) ∧
      (c : ℤ) ∣ intervalDisplacement (wordStepDisplacement h w) a b ∧
      ¬(c : ℤ) ∣ wordPrimeContribution h w p a b := by
  obtain ⟨c, a, b, hab, hb, hc, hd, hn⟩ := hp
  refine ⟨c, a, b, ?_, hab, hb, hc, hd, hn⟩
  intro heq
  subst c
  exact hn (prime_dvd_wordPrimeContribution h w p a b)

/-- Intersecting an interval-shaped occurrence set with a prefix gives an
explicit nonempty interval of indices. -/
lemma TuplePrimeIntervals.prefix_occurrences {w : List SignedStep}
    (hw : TuplePrimeIntervals w) (p n : ℕ) (hn : n ≤ w.length)
    (hp : ∃ j, j < n ∧ TuplePrimeAt w p j) :
    ∃ a b, a < b ∧ b ≤ n ∧ ∀ i, i < n →
      (TuplePrimeAt w p i ↔ a ≤ i ∧ i < b) := by
  classical
  let S := (range n).filter (TuplePrimeAt w p)
  have hS : S.Nonempty := by
    obtain ⟨j, hj, hpj⟩ := hp
    exact ⟨j, mem_filter.mpr ⟨mem_range.mpr hj, hpj⟩⟩
  let a := S.min' hS
  let b := S.max' hS + 1
  have haS : a ∈ S := min'_mem S hS
  have hbS : b - 1 ∈ S := by
    simpa only [b, Nat.add_sub_cancel] using max'_mem S hS
  have han := (mem_range.mp (mem_filter.mp haS).1)
  have hbn := (mem_range.mp (mem_filter.mp hbS).1)
  have hab : a < b := by
    have h := min'_le S (S.max' hS) (max'_mem S hS)
    dsimp [a, b]
    omega
  refine ⟨a, b, hab, by dsimp [b] at *; omega, ?_⟩
  intro i hi
  constructor
  · intro hpi
    have hiS : i ∈ S := mem_filter.mpr ⟨mem_range.mpr hi, hpi⟩
    exact ⟨min'_le S i hiS, Nat.lt_succ_of_le (le_max' S i hiS)⟩
  · rintro ⟨hai, hib⟩
    exact hw p a i (b - 1) hai (by omega) (by omega)
      (mem_filter.mp haS).2 (mem_filter.mp hbS).2

lemma wordPrimeContribution_restrict (h : ℕ) (w : List SignedStep) (p n a b : ℕ)
    (hbn : b ≤ n)
    (hp : ∀ i, i < n → (TuplePrimeAt w p i ↔ a ≤ i ∧ i < b)) :
    wordPrimeContribution h w p 0 n = intervalDisplacement (wordStepDisplacement h w) a b := by
  classical
  unfold wordPrimeContribution intervalDisplacement
  calc
    _ = ∑ i ∈ Ico a b, if TuplePrimeAt w p i then wordStepDisplacement h w i else 0 := by
      symm
      apply Finset.sum_subset (Ico_subset_Ico (Nat.zero_le a) hbn)
      intro i hi hin
      have hnot : ¬TuplePrimeAt w p i := by
        intro hpi
        exact hin (mem_Ico.mpr ((hp i (mem_Ico.mp hi).2).mp hpi))
      simp only [hnot, ite_false]
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      simp only [(hp i (lt_of_lt_of_le (mem_Ico.mp hi).2 hbn)).mpr
        ⟨(mem_Ico.mp hi).1, (mem_Ico.mp hi).2⟩, ite_true]

/-- Minimality forbids a reversed suffix starting at a strictly positive
index, when an internal initial segment is divisible by its final prime. -/
lemma MinimalWord.no_reversed_divisible_interval {h s : ℕ} {supply : ℕ → ℕ → Prop}
    {w : List SignedStep} (hw : MinimalWord (ForwardProhibited h s supply) w)
    {a c p : ℕ} (ha : 0 < a) (hac : a + 1 < c) (hc : c < w.length)
    (hp : TuplePrimeAt w p (w.length - 1)) (hnot : ¬TuplePrimeAt w p a) :
    ¬(p : ℤ) ∣ intervalDisplacement (wordStepDisplacement h w) a c := by
  intro hdiv
  have hpro := reversed_interval_forwardProhibited h s supply w hw.1.2.1 hw.1.2.2.1
    hw.1.2.2.2.1 hw.1.2.2.2.2.1 hac hc le_rfl hp hnot hdiv
  apply hw.2 (reverseWord (wordSlice w a w.length))
    (Or.inr (reverseWord_infix (wordSlice_infix w a w.length))) ?_ hpro
  rw [reverseWord_length, wordSlice_length w (by omega) le_rfl]
  omega

/-- Every label of a minimal prohibited word is active or has a nonzero
prefix contribution modulo an active label used at that departure. -/
theorem MinimalWord.active_dichotomy {h s : ℕ} {supply : ℕ → ℕ → Prop}
    {w : List SignedStep} (hw : MinimalWord (ForwardProhibited h s supply) w)
    (hnew : ∀ i, i + 1 < w.length →
      ∃ p, TuplePrimeAt w p (i + 1) ∧ ¬TuplePrimeAt w p i)
    (hoff : ∀ p i, (∃ j, TuplePrimeAt w p j) → i < w.length →
      ¬TuplePrimeAt w p i → ¬(p : ℤ) ∣ wordStepDisplacement h w i)
    (y : ℕ) (hy : ∃ j, TuplePrimeAt w y j) :
    ActivePrime h w y ∨ ∃ z i, ActivePrime h w z ∧ TuplePrimeAt w z i ∧
      ¬(z : ℤ) ∣ wordPrimeContribution h w y 0 i := by
  classical
  have hlen : 3 ≤ w.length := hw.1.1
  have hinter : TuplePrimeIntervals w := hw.1.2.2.2.2.1
  obtain ⟨z, hzlast', hzprev⟩ := hnew (w.length - 2) (by omega)
  have heqlast : w.length - 2 + 1 = w.length - 1 := by omega
  have hzlast : TuplePrimeAt w z (w.length - 1) := heqlast ▸ hzlast'
  have hzearly : ∀ i, i < w.length - 1 → ¬TuplePrimeAt w z i := by
    intro i hi hzi
    exact hzprev (hinter z i (w.length - 2) (w.length - 1)
      (by omega) (by omega) (by omega) hzi hzlast)
  have hzactive := hw.1.last_new_active hzlast hzearly hoff
  by_cases hypre : ∃ j, j < w.length - 1 ∧ TuplePrimeAt w y j
  · obtain ⟨a, b, hab, hbn, hyinterval⟩ :=
      hinter.prefix_occurrences y (w.length - 1) (by omega) hypre
    have hyeq := wordPrimeContribution_restrict h w y (w.length - 1) a b hbn hyinterval
    by_cases hzd : (z : ℤ) ∣ wordPrimeContribution h w y 0 (w.length - 1)
    · have hdiv : (z : ℤ) ∣ intervalDisplacement (wordStepDisplacement h w) a b := by
        rwa [hyeq] at hzd
      have hab2 : a + 1 < b := by
        by_contra hn
        have hb : b = a + 1 := by omega
        have hd := hoff z a ⟨w.length - 1, hzlast⟩ (by omega) (hzearly a (by omega))
        exact hd (by simpa only [hb, intervalDisplacement_singleton] using hdiv)
      have ha : a = 0 := by
        by_contra hn
        exact hw.no_reversed_divisible_interval (by omega) hab2 (by omega)
          hzlast (hzearly a (by omega)) hdiv
      obtain ⟨z', hz'one, hz'zero⟩ := hnew 0 (by omega)
      obtain ⟨a', b', hab', hb'b, hz'interval⟩ :=
        hinter.prefix_occurrences z' b (by omega) ⟨1, by omega, hz'one⟩
      have ha' : a' = 1 := by
        have hle := ((hz'interval 1 (by omega)).mp hz'one).1
        have hne : a' ≠ 0 := by
          intro heq
          have hp := (hz'interval a' (by omega)).mpr ⟨le_rfl, hab'⟩
          exact hz'zero (by simpa only [heq] using hp)
        omega
      have hzeq := wordPrimeContribution_restrict h w z' b a' b' hb'b hz'interval
      have hnonzero : ¬(z : ℤ) ∣ wordPrimeContribution h w z' 0 b := by
        intro hzero
        have hdiv' : (z : ℤ) ∣ intervalDisplacement (wordStepDisplacement h w) 1 b' := by
          simpa only [hzeq, ha'] using hzero
        have hb' : 2 < b' := by
          by_contra hn
          have hb'eq : b' = 1 + 1 := by omega
          exact (hoff z 1 ⟨w.length - 1, hzlast⟩ (by omega) (hzearly 1 (by omega)))
            (by simpa only [hb'eq, intervalDisplacement_singleton] using hdiv')
        exact hw.no_reversed_divisible_interval (by omega) hb' (by omega)
          hzlast (hzearly 1 (by omega)) hdiv'
      have hz'active : ActivePrime h w z' := by
        refine ⟨z, 0, b, by omega, by omega, ⟨w.length - 1, hzlast⟩, ?_, hnonzero⟩
        simpa only [ha] using hdiv
      right
      refine ⟨z', 1, hz'active, hz'one, ?_⟩
      have hyzero : TuplePrimeAt w y 0 := (hyinterval 0 (by omega)).mpr ⟨by omega, by omega⟩
      rw [wordPrimeContribution_eq_singleton h w y 0 1 0 (by simp) hyzero]
      · exact hoff z' 0 ⟨1, hz'one⟩ (by omega) hz'zero
      · intro i hi _
        have := mem_Ico.mp hi
        omega
    · exact Or.inr ⟨z, w.length - 1, hzactive, hzlast, hzd⟩
  · left
    have hyearly : ∀ i, i < w.length - 1 → ¬TuplePrimeAt w y i := by
      intro i hi hpi
      exact hypre ⟨i, hi, hpi⟩
    obtain ⟨j, hyj⟩ := hy
    have hj := hyj.index_lt
    have hjeq : j = w.length - 1 := by
      by_contra hn
      exact hyearly j (by omega) hyj
    exact hw.1.last_new_active (hjeq ▸ hyj) hyearly hoff

/-- Equal-size squarefree tuples that change must also acquire a new prime. -/
lemma adjacent_tuple_new_prime (w : List SignedStep) (J : ℕ)
    (hsq : ∀ a ∈ w, Squarefree a.tuple)
    (hcard : ∀ a ∈ w, a.tuple.primeFactors.card = J)
    (hchain : w.IsChain (fun a b => a.tuple ≠ b.tuple)) :
    ∀ i, i + 1 < w.length → ∃ p, TuplePrimeAt w p (i + 1) ∧ ¬TuplePrimeAt w p i := by
  intro i hi
  have hi0 : i < w.length := by omega
  have ha := List.getElem_mem hi0
  have hb := List.getElem_mem hi
  have hneq : w[i].tuple ≠ w[i + 1].tuple := (List.isChain_iff_getElem.mp hchain) i hi
  have hsets : w[i + 1].tuple.primeFactors ≠ w[i].tuple.primeFactors := by
    intro heq
    apply hneq
    calc
      _ = ∏ p ∈ w[i].tuple.primeFactors, p := (Nat.prod_primeFactors_of_squarefree (hsq _ ha)).symm
      _ = ∏ p ∈ w[i + 1].tuple.primeFactors, p := by rw [heq]
      _ = _ := Nat.prod_primeFactors_of_squarefree (hsq _ hb)
  have hnot : ¬w[i + 1].tuple.primeFactors ⊆ w[i].tuple.primeFactors := by
    intro hsub
    apply hsets
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard _ ha, hcard _ hb])
  obtain ⟨p, hpb, hpa⟩ := Finset.not_subset.mp hnot
  have hp := Nat.mem_primeFactors.mp hpb
  refine ⟨p, (tuplePrimeAt_iff_getElem w p (i + 1) hi).mpr ⟨hp.1, hp.2.1⟩, ?_⟩
  intro hpi
  have hpai := (tuplePrimeAt_iff_getElem w p i hi0).mp hpi
  exact hpa (Nat.mem_primeFactors.mpr ⟨hpai.1, hpai.2, (hsq _ ha).ne_zero⟩)

/-- The active-label dichotomy with the manuscript's concrete arithmetic
hypotheses: squarefree whole tuples of fixed prime-factor count, and prime
exclusion from the common multiplier and all padding factors. -/
theorem MinimalWord.active_dichotomy_of_squarefree {h s J : ℕ}
    {supply : ℕ → ℕ → Prop} {w : List SignedStep}
    (hw : MinimalWord (ForwardProhibited h s supply) w)
    (hsq : ∀ a ∈ w, Squarefree a.tuple)
    (hcard : ∀ a ∈ w, a.tuple.primeFactors.card = J)
    (hsupport : ∀ p j, TuplePrimeAt w p j → ¬p ∣ h ∧ ∀ a ∈ w, ¬p ∣ a.padding)
    (y : ℕ) (hy : ∃ j, TuplePrimeAt w y j) :
    ActivePrime h w y ∨ ∃ z i, ActivePrime h w z ∧ TuplePrimeAt w z i ∧
      ¬(z : ℤ) ∣ wordPrimeContribution h w y 0 i := by
  apply hw.active_dichotomy (adjacent_tuple_new_prime w J hsq hcard hw.1.2.2.2.1) ?_ y hy
  intro p i hseen hi hnot
  apply word_prime_support hsupport p i ?_ hi hnot
  obtain ⟨j, hj⟩ := hseen
  exact ⟨j, hj.index_lt, hj⟩

end TwoPointCorrelations

end OAI
