import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Tactic.Abel
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech

namespace OAI

namespace PiExponent.ProjectiveMonomialCechHigher

noncomputable section
open scoped BigOperators
open ProjectiveMonomialCech

variable {ι A K : Type*} [AddCommGroup A]

abbrev Cochain (ι A : Type*) (q : ℕ) := (Fin (q + 1) → ι) → A

def differential {q : ℕ} (c : Cochain ι A q) : Cochain ι A (q + 1) :=
  fun t => ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val • c (t ∘ k.succAbove)

theorem differential_cons {q : ℕ} (c : Cochain ι A (q + 1))
    (p : ι) (t : Fin (q + 2) → ι) :
    differential c (Fin.cons p t) =
      c t - differential (fun s : Fin (q + 1) → ι => c (Fin.cons p s)) t := by
  rw [differential, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ,
    Fin.succAbove_zero, Fin.cons_comp_succ, Fin.cons_comp_succ_succAbove]
  change c t + (∑ k : Fin (q + 2), (-1 : ℤ) ^ (k.val + 1) •
    c (Fin.cons p (t ∘ k.succAbove))) =
    c t - differential (fun s : Fin (q + 1) → ι => c (Fin.cons p s)) t
  rw [differential, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ, mul_neg_one, neg_zsmul]

theorem differential_sub {q : ℕ} (c e : Cochain ι A q) :
    differential (c - e) = differential c - differential e := by
  funext t
  simp only [differential, Pi.sub_apply, zsmul_sub, Finset.sum_sub_distrib]

@[simp] theorem differential_zero {q : ℕ} :
    differential (0 : Cochain ι A q) = 0 := by
  funext t
  simp only [differential, Pi.zero_apply, zsmul_zero, Finset.sum_const_zero]

theorem differential_squared {q : ℕ} (c : Cochain ι A q) :
    differential (differential c) = 0 := by
  induction q with
  | zero =>
      funext t
      simp only [differential, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_zsmul,
        Fin.val_succ, Fin.sum_univ_zero, add_zero]
      have hsingleton (f : Fin 1 → ι) : f = fun _ => f 0 := by
        funext i
        exact congrArg f (Subsingleton.elim i 0)
      simp only [hsingleton, Function.comp_apply]
      simp [Fin.succAbove]
      abel
  | succ q ih =>
      funext t
      let p := t 0
      let u := Fin.tail t
      have ht : t = Fin.cons p u := (Fin.cons_self_tail t).symm
      rw [ht, differential_cons]
      have hfun : (fun s : Fin (q + 1 + 1) → ι => differential c (Fin.cons p s)) =
          c - differential (fun s : Fin (q + 1) → ι => c (Fin.cons p s)) := by
        funext s
        exact differential_cons c p s
      rw [hfun, differential_sub, ih]
      simp

variable [Fintype ι] [AddCommGroup K]

def Regular {d : ℤ} {q : ℕ} (c : Cochain ι (Laurent ι K d) q) : Prop :=
  ∀ t, RegularOn (Set.range t) (c t)

def insertionSupport {d : ℤ} {q : ℕ} (c : Cochain ι (Laurent ι K d) (q + 1))
    (t : Fin (q + 1) → ι) : Finset (Monomial ι d) := by
  classical
  exact Finset.univ.biUnion fun p : ι => (c (Fin.cons p t)).support

def contraction {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (c : Cochain ι (Laurent ι K d) (q + 1)) : Cochain ι (Laurent ι K d) q := by
  classical
  exact fun t => Finsupp.onFinset (insertionSupport c t)
    (fun a => c (Fin.cons (pivot a) t) a)
    (fun a ha => Finset.mem_biUnion.mpr
      ⟨pivot a, Finset.mem_univ _, Finsupp.mem_support_iff.mpr ha⟩)

@[simp] theorem contraction_apply {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (c : Cochain ι (Laurent ι K d) (q + 1))
    (t : Fin (q + 1) → ι) (a : Monomial ι d) :
    contraction pivot c t a = c (Fin.cons (pivot a) t) a := rfl

theorem contraction_support_subset {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (c : Cochain ι (Laurent ι K d) (q + 1)) (t : Fin (q + 1) → ι) :
    (contraction pivot c t).support ⊆ insertionSupport c t := by
  classical
  exact Finsupp.support_onFinset_subset

theorem contraction_regular {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a))
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c) :
    Regular (contraction pivot c) := by
  intro t a ha k hk
  obtain ⟨j, hj⟩ := hc (Fin.cons (pivot a) t) a ha k hk
  cases j using Fin.cases with
  | zero =>
      simp only [Fin.cons_zero] at hj
      rw [← hj] at hk
      exact False.elim ((not_lt_of_ge (hpivot a)) hk)
  | succ j => exact ⟨j, by simpa only [Fin.cons_succ] using hj⟩

theorem differential_apply {d : ℤ} {q : ℕ} (c : Cochain ι (Laurent ι K d) q)
    (t : Fin (q + 2) → ι) (a : Monomial ι d) :
    differential c t a = differential (fun s => c s a) t := by
  simp only [differential, Finsupp.finsetSum_apply, Finsupp.smul_apply]

theorem differential_regular {d : ℤ} {q : ℕ}
    (c : Cochain ι (Laurent ι K d) q) (hc : Regular c) :
    Regular (differential c) := by
  intro t a ha k hk
  by_contra hnot
  apply ha
  rw [differential_apply]
  unfold differential
  apply Finset.sum_eq_zero
  intro i _
  have hz : c (t ∘ i.succAbove) a = 0 := by
    by_contra hne
    obtain ⟨j, hj⟩ := hc (t ∘ i.succAbove) a hne k hk
    exact hnot ⟨i.succAbove j, hj⟩
  change (-1 : ℤ) ^ i.val • c (t ∘ i.succAbove) a = 0
  rw [hz, smul_zero]

theorem contraction_identity {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (c : Cochain ι (Laurent ι K d) (q + 1)) :
    contraction pivot (differential c) + differential (contraction pivot c) = c := by
  funext t
  ext a
  simp only [Pi.add_apply, Finsupp.add_apply, contraction_apply, differential_apply]
  have h := differential_cons (fun s => c s a) (pivot a) t
  rw [h]
  exact sub_add_cancel _ _

theorem exact_of_pivot {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a))
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c)
    (hcocycle : differential c = 0) :
    ∃ b : Cochain ι (Laurent ι K d) q, Regular b ∧ differential b = c := by
  refine ⟨contraction pivot c, contraction_regular pivot hpivot c hc, ?_⟩
  have h := contraction_identity pivot c
  rw [hcocycle] at h
  have hz : contraction pivot (0 : Cochain ι (Laurent ι K d) (q + 2)) = 0 := by
    funext t
    ext a
    rfl
  rw [hz, zero_add] at h
  exact h

theorem nonnegative_twist_cech_exact_all_positive {d : ℤ} (hd : 0 ≤ d) {q : ℕ}
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c)
    (hcocycle : differential c = 0) :
    ∃ b : Cochain ι (Laurent ι K d) q, Regular b ∧ differential b = c := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
      refine ⟨fun t => isEmptyElim (t 0), ?_, ?_⟩
      · intro t
        exact isEmptyElim (t 0)
      · funext t
        exact isEmptyElim (t 0)
  | inr h =>
      let pivot : Monomial ι d → ι :=
        fun a => Classical.choose (exists_nonnegative_coordinate hd a)
      have hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a) :=
        fun a => Classical.choose_spec (exists_nonnegative_coordinate hd a)
      exact exact_of_pivot pivot hpivot c hc hcocycle

end
end PiExponent.ProjectiveMonomialCechHigher

end OAI
