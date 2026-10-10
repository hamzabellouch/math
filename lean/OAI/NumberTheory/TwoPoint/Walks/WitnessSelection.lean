import OAI.NumberTheory.TwoPoint.Bounds.ActiveLabels
import OAI.NumberTheory.TwoPoint.Walks.WitnessSupport

namespace OAI

/-!
# Selecting a triangular family of witness relations

The finite split in the singleton argument is performed on actual numerical
witness words. The comparison alternatives retain the neighboring witness,
its control prime, the selected internal departure, and the nonzero private
prime contribution at that departure.
-/

namespace TwoPointCorrelations

open Finset

noncomputable def freshActiveBefore {n : ℕ} (h : ℕ) (word : Fin n → List SignedStep)
    (i : Fin n) : Prop :=
  ∃ z, ActivePrime h (word i) z ∧ ∀ j : Fin n, j < i → z ∉ wordPrimeSupport (word j)

noncomputable def freshActiveAfter {n : ℕ} (h : ℕ) (word : Fin n → List SignedStep)
    (i : Fin n) : Prop :=
  ∃ z, ActivePrime h (word i) z ∧ ∀ j : Fin n, i < j → z ∉ wordPrimeSupport (word j)

/-- The internal active alternative and the two ordered comparison
alternatives needed for successive elimination. -/
theorem select_witness_relations {n K h s J : ℕ} {supply : ℕ → ℕ → Prop}
    (word : Fin n → List SignedStep) (mark : Fin n → ℕ)
    (attachment position : Fin n → ℕ)
    (hsize : 8 * K ≤ n)
    (hminimal : ∀ i, MinimalWord (ForwardProhibited h s supply) (word i))
    (hsq : ∀ i t, t ∈ word i → Squarefree t.tuple)
    (hcard : ∀ i t, t ∈ word i → t.tuple.primeFactors.card = J)
    (hsupport : ∀ i p j, TuplePrimeAt (word i) p j →
      ¬p ∣ h ∧ ∀ t ∈ word i, ¬p ∣ t.padding)
    (hmark : ∀ i, mark i ∈ wordPrimeSupport (word i))
    (hprivate : ∀ i j, j ≠ i → mark i ∉ wordPrimeSupport (word j)) :
    ∃ R : Finset (Fin n), K ≤ R.card ∧
      ((∀ i ∈ R, freshActiveBefore h word i) ∨
       (∀ i ∈ R, freshActiveAfter h word i) ∨
       (∀ i ∈ R, attachment i ≤ position i ∧
         ∃ z r j, j < i ∧ ActivePrime h (word i) z ∧ TuplePrimeAt (word i) z r ∧
           ¬(z : ℤ) ∣ wordPrimeContribution h (word i) (mark i) 0 r ∧
           z ∈ wordPrimeSupport (word j)) ∨
       (∀ i ∈ R, position i < attachment i ∧
         ∃ z r j, i < j ∧ ActivePrime h (word i) z ∧ TuplePrimeAt (word i) z r ∧
           ¬(z : ℤ) ∣ wordPrimeContribution h (word i) (mark i) 0 r ∧
           z ∈ wordPrimeSupport (word j))) := by
  classical
  let B : Finset (Fin n) := univ.filter (freshActiveBefore h word)
  let A : Finset (Fin n) := univ.filter (freshActiveAfter h word)
  let C : Finset (Fin n) := univ.filter (fun i =>
    i ∉ B ∧ i ∉ A ∧ attachment i ≤ position i)
  let D : Finset (Fin n) := univ.filter (fun i =>
    i ∉ B ∧ i ∉ A ∧ position i < attachment i)
  have hcover : B ∪ A ∪ C ∪ D = univ := by
    apply Finset.eq_univ_of_forall
    intro i
    by_cases hiB : i ∈ B
    · simp only [mem_union]; tauto
    by_cases hiA : i ∈ A
    · simp only [mem_union]; tauto
    by_cases hi : attachment i ≤ position i
    · have hiC : i ∈ C := mem_filter.mpr ⟨mem_univ _, hiB, hiA, hi⟩
      simp only [mem_union]; tauto
    · have hiD : i ∈ D := mem_filter.mpr ⟨mem_univ _, hiB, hiA, by omega⟩
      simp only [mem_union]; tauto
  have hcount : n ≤ B.card + A.card + C.card + D.card := by
    have hBA := card_union_le B A
    have hBAC := card_union_le (B ∪ A) C
    have hBACD := card_union_le (B ∪ A ∪ C) D
    rw [hcover, card_univ, Fintype.card_fin] at hBACD
    omega
  have hcompare (i : Fin n) (hiB : i ∉ B) (hiA : i ∉ A) :
      ∃ z r, ActivePrime h (word i) z ∧ TuplePrimeAt (word i) z r ∧
        ¬(z : ℤ) ∣ wordPrimeContribution h (word i) (mark i) 0 r ∧
        (∃ j : Fin n, j < i ∧ z ∈ wordPrimeSupport (word j)) ∧
        (∃ j : Fin n, i < j ∧ z ∈ wordPrimeSupport (word j)) := by
    have hnotactive : ¬ActivePrime h (word i) (mark i) := by
      intro ha
      apply hiB
      exact mem_filter.mpr ⟨mem_univ _, mark i, ha,
        fun j hji => hprivate i j (ne_of_lt hji)⟩
    have hocc := (mem_wordPrimeSupport_iff (mark i) (word i) (hsq i)).mp (hmark i)
    rcases (hminimal i).active_dichotomy_of_squarefree (hsq i) (hcard i) (hsupport i)
      (mark i) hocc with ha | ⟨z, r, hz, hzr, hn⟩
    · exact False.elim (hnotactive ha)
    · refine ⟨z, r, hz, hzr, hn, ?_, ?_⟩
      · by_contra! hj
        exact hiB (mem_filter.mpr ⟨mem_univ _, z, hz, hj⟩)
      · by_contra! hj
        exact hiA (mem_filter.mpr ⟨mem_univ _, z, hz, hj⟩)
  by_cases hB : K ≤ B.card
  · exact ⟨B, hB, Or.inl (fun i hi => (mem_filter.mp hi).2)⟩
  by_cases hA : K ≤ A.card
  · exact ⟨A, hA, Or.inr (Or.inl (fun i hi => (mem_filter.mp hi).2))⟩
  by_cases hC : K ≤ C.card
  · refine ⟨C, hC, Or.inr (Or.inr (Or.inl ?_))⟩
    intro i hi
    rcases (mem_filter.mp hi).2 with ⟨hiB, hiA, htime⟩
    obtain ⟨z, r, hz, hzr, hn, ⟨j, hji, hzj⟩, _⟩ := hcompare i hiB hiA
    exact ⟨htime, z, r, j, hji, hz, hzr, hn, hzj⟩
  · have hD : K ≤ D.card := by omega
    refine ⟨D, hD, Or.inr (Or.inr (Or.inr ?_))⟩
    intro i hi
    rcases (mem_filter.mp hi).2 with ⟨hiB, hiA, htime⟩
    obtain ⟨z, r, hz, hzr, hn, _, ⟨j, hij, hzj⟩⟩ := hcompare i hiB hiA
    exact ⟨htime, z, r, j, hij, hz, hzr, hn, hzj⟩

lemma wordPrimeContribution_zero_of_not_mem (h : ℕ) (w : List SignedStep) (p a b : ℕ)
    (hsq : ∀ t ∈ w, Squarefree t.tuple) (hp : p ∉ wordPrimeSupport w) :
    wordPrimeContribution h w p a b = 0 := by
  classical
  unfold wordPrimeContribution
  apply sum_eq_zero
  intro i _
  have hnot : ¬TuplePrimeAt w p i := fun hpi =>
    hp ((mem_wordPrimeSupport_iff p w hsq).mpr ⟨i, hpi⟩)
  simp only [hnot, ite_false]

lemma ActivePrime.mem_wordPrimeSupport {h p : ℕ} {w : List SignedStep}
    (hp : ActivePrime h w p) (hsq : ∀ t ∈ w, Squarefree t.tuple) :
    p ∈ wordPrimeSupport w := by
  by_contra hnot
  obtain ⟨c, a, b, _, _, _, _, hnonzero⟩ := hp
  apply hnonzero
  rw [wordPrimeContribution_zero_of_not_mem h w p a b hsq hnot]
  exact dvd_zero _

/-- Fresh active labels can be chosen injectively. Earlier internal relations
contain none of the later chosen variables. -/
theorem select_fresh_before_labels {n h : ℕ} (word : Fin n → List SignedStep)
    (R : Finset (Fin n)) (hsq : ∀ i t, t ∈ word i → Squarefree t.tuple)
    (hfresh : ∀ i ∈ R, freshActiveBefore h word i) :
    ∃ z : R → ℕ, Function.Injective z ∧
      (∀ i : R, ActivePrime h (word i) (z i)) ∧
      ∀ i j : R, i.val < j.val → z j ∉ wordPrimeSupport (word i) := by
  classical
  have hex (i : R) : ∃ z, ActivePrime h (word i) z ∧
      ∀ j : Fin n, j < i.val → z ∉ wordPrimeSupport (word j) := hfresh i i.property
  choose z hz using hex
  refine ⟨z, ?_, (fun i => (hz i).1), fun i j hij => (hz j).2 i hij⟩
  intro i j heq
  apply Subtype.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact (hz j).2 i hij (heq ▸ (hz i).1.mem_wordPrimeSupport (hsq i))
  · exact (hz i).2 j hji (heq.symm ▸ (hz j).1.mem_wordPrimeSupport (hsq j))

/-- The reversed order gives the other internal triangular system. -/
theorem select_fresh_after_labels {n h : ℕ} (word : Fin n → List SignedStep)
    (R : Finset (Fin n)) (hsq : ∀ i t, t ∈ word i → Squarefree t.tuple)
    (hfresh : ∀ i ∈ R, freshActiveAfter h word i) :
    ∃ z : R → ℕ, Function.Injective z ∧
      (∀ i : R, ActivePrime h (word i) (z i)) ∧
      ∀ i j : R, j.val < i.val → z j ∉ wordPrimeSupport (word i) := by
  classical
  have hex (i : R) : ∃ z, ActivePrime h (word i) z ∧
      ∀ j : Fin n, i.val < j → z ∉ wordPrimeSupport (word j) := hfresh i i.property
  choose z hz using hex
  refine ⟨z, ?_, (fun i => (hz i).1), fun i j hji => (hz j).2 i hji⟩
  intro i j heq
  apply Subtype.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact (hz i).2 j hij (heq.symm ▸ (hz j).1.mem_wordPrimeSupport (hsq j))
  · exact (hz j).2 i hji (heq ▸ (hz i).1.mem_wordPrimeSupport (hsq i))

/-- A prime shared by two different witnesses is none of their family's
private marked primes. This includes the comparison's controlling prime. -/
lemma shared_prime_ne_private {n : ℕ} (word : Fin n → List SignedStep)
    (mark : Fin n → ℕ)
    (hprivate : ∀ i j, j ≠ i → mark i ∉ wordPrimeSupport (word j))
    {i j : Fin n} (hij : i ≠ j) {z : ℕ}
    (hi : z ∈ wordPrimeSupport (word i)) (hj : z ∈ wordPrimeSupport (word j)) :
    ∀ k, z ≠ mark k := by
  intro k heq
  by_cases hki : k = i
  · subst k
    exact hprivate i j hij.symm (heq ▸ hj)
  · exact hprivate k i (fun heq => hki heq.symm) (heq ▸ hi)

/-- In the earlier-comparison case, every later selected private label is
absent from both witness prefixes and from the entire main segment. -/
lemma earlier_comparison_excludes_later {n : ℕ} (word : Fin n → List SignedStep)
    (mark : Fin n → ℕ) (attachment position : Fin n → ℕ)
    (horder : Monotone attachment)
    (hprivate : ∀ i j, j ≠ i → mark i ∉ wordPrimeSupport (word j))
    {i j k : Fin n} (hji : j < i) (hik : i < k) (hpos : attachment k ≤ position k) :
    mark k ∉ wordPrimeSupport (word i) ∧ mark k ∉ wordPrimeSupport (word j) ∧
      ∀ v ∈ Ico (attachment j) (attachment i), v ≠ position k := by
  refine ⟨hprivate k i (ne_of_lt hik), hprivate k j (ne_of_lt (hji.trans hik)), ?_⟩
  intro v hv heq
  have hle := horder hik.le
  have hv' := (mem_Ico.mp hv).2
  omega

/-- In the later-comparison case, reverse attachment order gives the same
absence for every still-to-be-eliminated private variable. -/
lemma later_comparison_excludes_earlier {n : ℕ} (word : Fin n → List SignedStep)
    (mark : Fin n → ℕ) (attachment position : Fin n → ℕ)
    (horder : Monotone attachment)
    (hprivate : ∀ i j, j ≠ i → mark i ∉ wordPrimeSupport (word j))
    {i j k : Fin n} (hij : i < j) (hki : k < i) (hpos : position k < attachment k) :
    mark k ∉ wordPrimeSupport (word i) ∧ mark k ∉ wordPrimeSupport (word j) ∧
      ∀ v ∈ Ico (attachment i) (attachment j), v ≠ position k := by
  refine ⟨hprivate k i (ne_of_gt hki), hprivate k j (ne_of_gt (hki.trans hij)), ?_⟩
  intro v hv heq
  have hle := horder hki.le
  have hv' := (mem_Ico.mp hv).1
  omega

/-- Positivity at two departures in the same configuration gives the exact
comparison congruence used by the selected triangular systems. -/
lemma PositiveWord.comparison_relation {h p ri rj : ℕ} {xi xj : ℤ}
    {wi wj : List SignedStep} (hi : PositiveWord h xi wi) (hj : PositiveWord h xj wj)
    (hpi : TuplePrimeAt wi p ri) (hpj : TuplePrimeAt wj p rj) :
    (p : ℤ) ∣ (xi + wordDisplacement h (wi.take ri)) -
      (xj + wordDisplacement h (wj.take rj)) :=
  (hi.tuplePrime_departure hpi).sub (hj.tuplePrime_departure hpj)

lemma wordPrimeContribution_zero_of_avoids (h : ℕ) (w : List SignedStep) (p a b : ℕ)
    (hp : ∀ i ∈ Ico a b, ¬TuplePrimeAt w p i) :
    wordPrimeContribution h w p a b = 0 := by
  classical
  unfold wordPrimeContribution
  apply sum_eq_zero
  intro i hi
  simp only [hp i hi, ite_false]

lemma wordPrimeContribution_zero_of_unique_position (h : ℕ) (w : List SignedStep)
    (p a b position : ℕ) (hunique : ∀ i, TuplePrimeAt w p i → i = position)
    (hposition : ∀ i ∈ Ico a b, i ≠ position) :
    wordPrimeContribution h w p a b = 0 := by
  apply wordPrimeContribution_zero_of_avoids
  intro i hi hpi
  exact hposition i hi (hunique i hpi)

lemma PositiveWord.main_comparison_relation {h p ai aj ri rj : ℕ} {x : ℤ}
    {main wi wj : List SignedStep} (haji : aj ≤ ai)
    (hi : PositiveWord h (x + wordDisplacement h (main.take ai)) wi)
    (hj : PositiveWord h (x + wordDisplacement h (main.take aj)) wj)
    (hpi : TuplePrimeAt wi p ri) (hpj : TuplePrimeAt wj p rj) :
    (p : ℤ) ∣ intervalDisplacement (wordStepDisplacement h main) aj ai +
      wordDisplacement h (wi.take ri) - wordDisplacement h (wj.take rj) := by
  have hr := hi.comparison_relation hj hpi hpj
  rw [intervalDisplacement_eq_sub _ haji]
  simp only [wordDisplacement_take] at hr ⊢
  convert hr using 1
  ring

/-- The private selected prime has exactly its designated nonzero prefix
contribution in an earlier comparison; all other contributions vanish. -/
lemma earlier_comparison_private_contribution {n h : ℕ}
    (main : List SignedStep) (word : Fin n → List SignedStep) (mark : Fin n → ℕ)
    (attachment position : Fin n → ℕ)
    (hsq : ∀ i t, t ∈ word i → Squarefree t.tuple)
    (hprivate : ∀ i j, j ≠ i → mark i ∉ wordPrimeSupport (word j))
    (hmain : ∀ i v, TuplePrimeAt main (mark i) v → v = position i)
    {i j : Fin n} (hji : j < i) (hpos : attachment i ≤ position i)
    (ri rj : ℕ) :
    wordPrimeContribution h main (mark i) (attachment j) (attachment i) +
      wordPrimeContribution h (word i) (mark i) 0 ri -
      wordPrimeContribution h (word j) (mark i) 0 rj =
      wordPrimeContribution h (word i) (mark i) 0 ri := by
  have hm : wordPrimeContribution h main (mark i) (attachment j) (attachment i) = 0 := by
    apply wordPrimeContribution_zero_of_unique_position h main (mark i) _ _ (position i) (hmain i)
    intro v hv heq
    have hv' := (mem_Ico.mp hv).2
    omega
  have hjzero := wordPrimeContribution_zero_of_not_mem h (word j) (mark i) 0 rj
    (hsq j) (hprivate i j (ne_of_lt hji))
  rw [hm, hjzero]
  ring

/-- The later comparison changes the selected prefix's sign, preserving its
nonvanishing modulo the controlling prime. -/
lemma later_comparison_private_contribution {n h : ℕ}
    (main : List SignedStep) (word : Fin n → List SignedStep) (mark : Fin n → ℕ)
    (attachment position : Fin n → ℕ)
    (hsq : ∀ i t, t ∈ word i → Squarefree t.tuple)
    (hprivate : ∀ i j, j ≠ i → mark i ∉ wordPrimeSupport (word j))
    (hmain : ∀ i v, TuplePrimeAt main (mark i) v → v = position i)
    {i j : Fin n} (hij : i < j) (hpos : position i < attachment i)
    (ri rj : ℕ) :
    wordPrimeContribution h main (mark i) (attachment i) (attachment j) +
      wordPrimeContribution h (word j) (mark i) 0 rj -
      wordPrimeContribution h (word i) (mark i) 0 ri =
      -wordPrimeContribution h (word i) (mark i) 0 ri := by
  have hm : wordPrimeContribution h main (mark i) (attachment i) (attachment j) = 0 := by
    apply wordPrimeContribution_zero_of_unique_position h main (mark i) _ _ (position i) (hmain i)
    intro v hv heq
    have hv' := (mem_Ico.mp hv).1
    omega
  have hjzero := wordPrimeContribution_zero_of_not_mem h (word j) (mark i) 0 rj
    (hsq j) (hprivate i j (ne_of_gt hij))
  rw [hm, hjzero]
  ring

end TwoPointCorrelations

end OAI
