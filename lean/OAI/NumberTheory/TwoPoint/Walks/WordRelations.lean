import OAI.NumberTheory.TwoPoint.Bounds.LabeledPrimeWords

namespace OAI

/-! Concrete internal and comparison congruences as prime-variable relations. -/

namespace TwoPointCorrelations

open Finset

variable {ι τ σ : Type*} [DecidableEq ι] [Fintype τ] [Fintype σ]

def relationAdd (m : τ → PrimeMonomial ι) (n : σ → PrimeMonomial ι) : τ ⊕ σ → PrimeMonomial ι :=
  Sum.elim m n

def relationNeg (m : τ → PrimeMonomial ι) (t : τ) : PrimeMonomial ι :=
  ⟨-(m t).coefficient, (m t).labels⟩

omit [DecidableEq ι] in
lemma relationAdd_eval (m : τ → PrimeMonomial ι) (n : σ → PrimeMonomial ι) (x : ι → ℤ) :
    primeRelationEval (relationAdd m n) x = primeRelationEval m x + primeRelationEval n x := by
  simp [primeRelationEval, relationAdd, Fintype.sum_sum_type]

omit [DecidableEq ι] in
lemma relationNeg_eval (m : τ → PrimeMonomial ι) (x : ι → ℤ) :
    primeRelationEval (relationNeg m) x = -primeRelationEval m x := by
  simp [primeRelationEval, relationNeg, PrimeMonomial.eval]

lemma relationAdd_contribution (m : τ → PrimeMonomial ι) (n : σ → PrimeMonomial ι)
    (y : ι) (x : ι → ℤ) :
    primeRelationContribution (relationAdd m n) y x =
      primeRelationContribution m y x + primeRelationContribution n y x := by
  simp only [primeRelationContribution, relationAdd, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  congr 1

lemma relationNeg_contribution (m : τ → PrimeMonomial ι) (y : ι) (x : ι → ℤ) :
    primeRelationContribution (relationNeg m) y x = -primeRelationContribution m y x := by
  unfold primeRelationContribution
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro t _
  by_cases ht : y ∈ (m t).labels <;> simp [relationNeg, PrimeMonomial.eval, ht]

lemma relationAdd_support (m : τ → PrimeMonomial ι) (n : σ → PrimeMonomial ι) :
    primeRelationSupport (relationAdd m n) = primeRelationSupport m ∪ primeRelationSupport n := by
  ext y
  simp [primeRelationSupport, relationAdd, Sum.exists]

lemma relationNeg_support (m : τ → PrimeMonomial ι) :
    primeRelationSupport (relationNeg m) = primeRelationSupport m := rfl

namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
lemma occurrence_has_label (w : LabeledPrimeWord ι) (value : ι → ℕ)
    (hprime : ∀ j, (value j).Prime) (hw : w.Realizes value)
    (p : ℕ) (i : Fin w.word.length) (hp : TuplePrimeAt w.word p i) :
    ∃ c ∈ w.labels i, value c = p := by
  rw [tuplePrimeAt_iff_getElem w.word p i i.isLt, ← hw i] at hp
  obtain ⟨c, hc, hpc⟩ := (hp.1.prime.dvd_finsetProd_iff value).mp hp.2
  exact ⟨c, hc, ((Nat.prime_dvd_prime_iff_eq hp.1 (hprime c)).mp hpc).symm⟩

/-- The active numerical relation supplies a concrete interval polynomial
with the required nonzero coefficient and a distinct controlling label. -/
theorem active_relation (w : LabeledPrimeWord ι) (h : ℕ) (value : ι → ℕ)
    (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hw : w.Realizes value) (y : ι) (hy : ActivePrime h w.word (value y)) :
    ∃ c a b, c ≠ y ∧ a ≤ b ∧ b ≤ w.word.length ∧
      primeRelationEvent (w.intervalRelation h a b) y c (fun j => (value j : ℤ)) := by
  obtain ⟨p, a, b, hpy, hab, hb, ⟨r, hpr⟩, hdiv, hnonzero⟩ := hy.distinct_controller
  obtain ⟨c, _, hc⟩ := w.occurrence_has_label value hprime hw p ⟨r, hpr.index_lt⟩ hpr
  refine ⟨c, a, b, ?_, hab, hb, ?_, ?_⟩
  · intro heq
    exact hpy (by simpa only [heq] using hc.symm)
  · rw [w.intervalRelation_eval h a b value hw hb]
    change (value c : ℤ) ∣ _
    simpa only [hc] using hdiv
  · apply primeRelation_coefficient_nondegenerate
    rw [w.intervalRelation_contribution h a b value hinj hprime hw hb y]
    change ¬(value c : ℤ) ∣ _
    simpa only [hc] using hnonzero

lemma intervalRelation_not_mem (w : LabeledPrimeWord ι) (h a b : ℕ)
    (value : ι → ℕ) (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hw : w.Realizes value) (y : ι)
    (hno : ∀ r, a ≤ r → r < b → ¬TuplePrimeAt w.word (value y) r) :
    y ∉ primeRelationSupport (w.intervalRelation h a b) := by
  intro hy
  obtain ⟨r, har, hrb, hyr⟩ := (w.intervalRelation_support h a b y).mp hy
  exact hno r har hrb ((w.label_iff_occurrence value hinj hprime hw y r).mp hyr)

end LabeledPrimeWord

/-- The three contiguous parts of the earlier-departure comparison. -/
def comparisonRelation {ι : Type*} [DecidableEq ι]
    (main wi wj : LabeledPrimeWord ι) (h aj ai ri rj : ℕ) :=
  relationAdd (main.intervalRelation h aj ai)
    (relationAdd (wi.intervalRelation h 0 ri) (relationNeg (wj.intervalRelation h 0 rj)))

lemma comparisonRelation_eval {ι : Type*} [DecidableEq ι]
    (main wi wj : LabeledPrimeWord ι) (h aj ai ri rj : ℕ) (value : ι → ℕ)
    (hm : main.Realizes value) (hi : wi.Realizes value) (hj : wj.Realizes value)
    (hai : ai ≤ main.word.length) (hri : ri ≤ wi.word.length) (hrj : rj ≤ wj.word.length) :
    primeRelationEval (comparisonRelation main wi wj h aj ai ri rj) (fun j => (value j : ℤ)) =
      intervalDisplacement (wordStepDisplacement h main.word) aj ai +
        wordDisplacement h (wi.word.take ri) - wordDisplacement h (wj.word.take rj) := by
  rw [comparisonRelation, relationAdd_eval, relationAdd_eval, relationNeg_eval,
    main.intervalRelation_eval h aj ai value hm hai,
    wi.intervalRelation_eval h 0 ri value hi hri, wj.intervalRelation_eval h 0 rj value hj hrj]
  simp only [intervalDisplacement, Nat.Ico_zero_eq_range, wordDisplacement_take]
  ring

lemma comparisonRelation_contribution {ι : Type*} [DecidableEq ι]
    (main wi wj : LabeledPrimeWord ι) (h aj ai ri rj : ℕ) (value : ι → ℕ)
    (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hm : main.Realizes value) (hi : wi.Realizes value) (hj : wj.Realizes value)
    (hai : ai ≤ main.word.length) (hri : ri ≤ wi.word.length) (hrj : rj ≤ wj.word.length) (y : ι) :
    primeRelationContribution (comparisonRelation main wi wj h aj ai ri rj) y
        (fun j => (value j : ℤ)) =
      wordPrimeContribution h main.word (value y) aj ai +
        wordPrimeContribution h wi.word (value y) 0 ri -
        wordPrimeContribution h wj.word (value y) 0 rj := by
  rw [comparisonRelation, relationAdd_contribution, relationAdd_contribution, relationNeg_contribution,
    main.intervalRelation_contribution h aj ai value hinj hprime hm hai y,
    wi.intervalRelation_contribution h 0 ri value hinj hprime hi hri y,
    wj.intervalRelation_contribution h 0 rj value hinj hprime hj hrj y]
  ring

lemma comparisonRelation_not_mem {ι : Type*} [DecidableEq ι]
    (main wi wj : LabeledPrimeWord ι) (h aj ai ri rj : ℕ) (value : ι → ℕ)
    (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hm : main.Realizes value) (hi : wi.Realizes value) (hj : wj.Realizes value) (y : ι)
    (hmain : ∀ r, aj ≤ r → r < ai → ¬TuplePrimeAt main.word (value y) r)
    (hwi : ∀ r, ¬TuplePrimeAt wi.word (value y) r)
    (hwj : ∀ r, ¬TuplePrimeAt wj.word (value y) r) :
    y ∉ primeRelationSupport (comparisonRelation main wi wj h aj ai ri rj) := by
  rw [comparisonRelation, relationAdd_support, relationAdd_support, relationNeg_support]
  simp only [mem_union, not_or]
  exact ⟨main.intervalRelation_not_mem h aj ai value hinj hprime hm y hmain,
    wi.intervalRelation_not_mem h 0 ri value hinj hprime hi y (fun r _ _ => hwi r),
    wj.intervalRelation_not_mem h 0 rj value hinj hprime hj y (fun r _ _ => hwj r)⟩

/-- Simultaneous positivity supplies the comparison congruence, and the
exact selected contribution supplies its retained nondegeneracy test. -/
lemma comparisonRelation_event {ι : Type*} [DecidableEq ι]
    (main wi wj : LabeledPrimeWord ι) (h aj ai ri rj : ℕ) (value : ι → ℕ)
    (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hm : main.Realizes value) (hi : wi.Realizes value) (hj : wj.Realizes value)
    (hai : ai ≤ main.word.length) (haji : aj ≤ ai) (x : ℤ) (selected control : ι)
    (hwi : PositiveWord h (x + wordDisplacement h (main.word.take ai)) wi.word)
    (hwj : PositiveWord h (x + wordDisplacement h (main.word.take aj)) wj.word)
    (hci : TuplePrimeAt wi.word (value control) ri)
    (hcj : TuplePrimeAt wj.word (value control) rj)
    (hnonzero : ¬(value control : ℤ) ∣
      wordPrimeContribution h main.word (value selected) aj ai +
        wordPrimeContribution h wi.word (value selected) 0 ri -
        wordPrimeContribution h wj.word (value selected) 0 rj) :
    primeRelationEvent (comparisonRelation main wi wj h aj ai ri rj) selected control
      (fun j => (value j : ℤ)) := by
  constructor
  · rw [comparisonRelation_eval main wi wj h aj ai ri rj value hm hi hj hai
      hci.index_lt.le hcj.index_lt.le]
    exact hwi.main_comparison_relation haji hwj hci hcj
  · apply primeRelation_coefficient_nondegenerate
    rw [comparisonRelation_contribution main wi wj h aj ai ri rj value hinj hprime hm hi hj
      hai hci.index_lt.le hcj.index_lt.le selected]
    exact hnonzero

end TwoPointCorrelations

end OAI
