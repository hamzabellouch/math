import OAI.NumberTheory.TwoPoint.Bounds.ReciprocalSampling
import OAI.NumberTheory.TwoPoint.Walks.WitnessSelection
import Mathlib.Algebra.BigOperators.Associated

namespace OAI

/-! Identifying squarefree-label polynomials with numerical signed words. -/

namespace TwoPointCorrelations

open Finset

structure LabeledPrimeWord (ι : Type*) where
  word : List SignedStep
  labels : Fin word.length → Finset ι

namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

def Realizes (w : LabeledPrimeWord ι) (value : ι → ℕ) : Prop :=
  ∀ i, ∏ j ∈ w.labels i, value j = (w.word[i.val]'i.isLt).tuple

def monomial (w : LabeledPrimeWord ι) (h : ℕ) (i : Fin w.word.length) : PrimeMonomial ι where
  coefficient := (if (w.word[i.val]'i.isLt).forward then 1 else -1) * (h : ℤ) * (w.word[i.val]'i.isLt).padding
  labels := w.labels i

omit [DecidableEq ι] in
lemma monomial_eval (w : LabeledPrimeWord ι) (h : ℕ) (value : ι → ℕ)
    (hw : w.Realizes value) (i : Fin w.word.length) :
    (w.monomial h i).eval (fun j => (value j : ℤ)) = wordStepDisplacement h w.word i := by
  rw [wordStepDisplacement_getElem h w.word i i.isLt]
  unfold monomial PrimeMonomial.eval SignedStep.displacement
  rw [← Nat.cast_prod, hw i]

omit [DecidableEq ι] in
lemma label_iff_occurrence (w : LabeledPrimeWord ι) (value : ι → ℕ)
    (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hw : w.Realizes value) (y : ι) (i : Fin w.word.length) :
    y ∈ w.labels i ↔ TuplePrimeAt w.word (value y) i := by
  rw [tuplePrimeAt_iff_getElem w.word (value y) i i.isLt, ← hw i]
  constructor
  · intro hy
    exact ⟨hprime y, Finset.dvd_prod_of_mem value hy⟩
  · rintro ⟨_, hy⟩
    obtain ⟨j, hj, hyj⟩ := ((hprime y).prime.dvd_finsetProd_iff value).mp hy
    have heq := hinj ((Nat.prime_dvd_prime_iff_eq (hprime y) (hprime j)).mp hyj)
    exact heq.symm ▸ hj

/-- A genuine interval relation; omitted steps have empty supports as well
as zero coefficients. This matters for the later-variable exclusion. -/
def intervalRelation (w : LabeledPrimeWord ι) (h a b : ℕ) (i : Fin w.word.length) : PrimeMonomial ι :=
  if a ≤ i.val ∧ i.val < b then w.monomial h i else ⟨0, ∅⟩

lemma intervalRelation_support (w : LabeledPrimeWord ι) (h a b : ℕ) (y : ι) :
    y ∈ primeRelationSupport (w.intervalRelation h a b) ↔
      ∃ i : Fin w.word.length, a ≤ i.val ∧ i.val < b ∧ y ∈ w.labels i := by
  simp only [primeRelationSupport, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hab : a ≤ i.val ∧ i.val < b
    · exact ⟨i, hab.1, hab.2, by simpa only [intervalRelation, ite_eq_left hab, monomial] using hi⟩
    · simp only [intervalRelation, ite_eq_right hab, notMem_empty] at hi
  · rintro ⟨i, hai, hib, hi⟩
    exact ⟨i, by simpa only [intervalRelation, ite_eq_left (And.intro hai hib), monomial] using hi⟩

end LabeledPrimeWord

lemma sum_fin_interval (n a b : ℕ) (D : ℕ → ℤ) (hb : b ≤ n) :
    (∑ i : Fin n, if a ≤ i.val ∧ i.val < b then D i.val else 0) = ∑ i ∈ Ico a b, D i := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if a ≤ i ∧ i < b then D i else 0) n]
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range, mem_Ico]
  omega

namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
lemma intervalRelation_eval (w : LabeledPrimeWord ι) (h a b : ℕ) (value : ι → ℕ)
    (hw : w.Realizes value) (hb : b ≤ w.word.length) :
    primeRelationEval (w.intervalRelation h a b) (fun j => (value j : ℤ)) =
      intervalDisplacement (wordStepDisplacement h w.word) a b := by
  unfold primeRelationEval
  have ht (i : Fin w.word.length) :
      (w.intervalRelation h a b i).eval (fun j => (value j : ℤ)) =
        if a ≤ i.val ∧ i.val < b then wordStepDisplacement h w.word i.val else 0 := by
    by_cases hi : a ≤ i.val ∧ i.val < b
    · simp only [intervalRelation, ite_eq_left hi]
      exact w.monomial_eval h value hw i
    · simp only [intervalRelation, ite_eq_right hi, PrimeMonomial.eval, zero_mul]
  simp_rw [ht]
  exact sum_fin_interval _ _ _ _ hb

lemma intervalRelation_contribution (w : LabeledPrimeWord ι) (h a b : ℕ)
    (value : ι → ℕ) (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hw : w.Realizes value) (hb : b ≤ w.word.length) (y : ι) :
    primeRelationContribution (w.intervalRelation h a b) y (fun j => (value j : ℤ)) =
      wordPrimeContribution h w.word (value y) a b := by
  classical
  unfold primeRelationContribution
  have ht (i : Fin w.word.length) :
      (if y ∈ (w.intervalRelation h a b i).labels
        then (w.intervalRelation h a b i).eval (fun j => (value j : ℤ)) else 0) =
      if a ≤ i.val ∧ i.val < b then
        (if TuplePrimeAt w.word (value y) i.val then wordStepDisplacement h w.word i.val else 0)
      else 0 := by
    by_cases hi : a ≤ i.val ∧ i.val < b
    · simp only [intervalRelation, ite_eq_left hi, monomial]
      by_cases hy : y ∈ w.labels i
      · have hp := (w.label_iff_occurrence value hinj hprime hw y i).mp hy
        simp only [hy, hp, ite_true]
        exact w.monomial_eval h value hw i
      · have hp : ¬TuplePrimeAt w.word (value y) i.val := fun hp =>
          hy ((w.label_iff_occurrence value hinj hprime hw y i).mpr hp)
        simp only [hy, hp, ite_false]
    · simp only [intervalRelation, ite_eq_right hi, notMem_empty, ite_false]
  simp_rw [ht]
  unfold wordPrimeContribution
  exact sum_fin_interval w.word.length a b
    (fun i => if TuplePrimeAt w.word (value y) i then wordStepDisplacement h w.word i else 0) hb

/-- A canonical finite label model, using the actual prime factors of each
whole tuple inside one finite prime pool. -/
def fromPrimeSet (word : List SignedStep) (P : Finset ℕ) : LabeledPrimeWord P where
  word := word
  labels i := univ.filter (fun p : P => p.val ∈ word[i].tuple.primeFactors)

lemma fromPrimeSet_realizes (word : List SignedStep) (P : Finset ℕ)
    (hsq : ∀ t ∈ word, Squarefree t.tuple)
    (hpool : ∀ t ∈ word, t.tuple.primeFactors ⊆ P) :
    (fromPrimeSet word P).Realizes Subtype.val := by
  intro i
  have hiword : word[i] ∈ word := List.getElem_mem i.isLt
  have himage : ((fromPrimeSet word P).labels i).image Subtype.val = word[i].tuple.primeFactors := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
      exact (mem_filter.mp hq).2
    · intro hp
      exact mem_image.mpr ⟨⟨p, hpool _ hiword hp⟩, mem_filter.mpr ⟨mem_univ _, hp⟩, rfl⟩
  calc
    _ = ∏ p ∈ word[i].tuple.primeFactors, p := by
      rw [← himage, prod_image]
      exact fun a _ b _ hab => Subtype.ext hab
    _ = _ := Nat.prod_primeFactors_of_squarefree (hsq _ hiword)

end LabeledPrimeWord

end TwoPointCorrelations

end OAI
