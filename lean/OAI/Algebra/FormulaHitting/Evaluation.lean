import OAI.Algebra.FormulaHitting.Formula
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic

namespace OAI

namespace NCHitting

local instance {n : ℕ} : DecidableEq (FreeMonoid (Fin n)) :=
  inferInstanceAs (DecidableEq (List (Fin n)))

private def wordCuts {n : ℕ} (w : Word n) :
    Finset (FreeMonoid (Fin n) × FreeMonoid (Fin n)) :=
  (Finset.range (w.length + 1)).image fun k =>
    (FreeMonoid.ofList (w.take k), FreeMonoid.ofList (w.drop k))

private theorem mem_wordCuts {n : ℕ} (w : Word n)
    (p : FreeMonoid (Fin n) × FreeMonoid (Fin n)) :
    p ∈ wordCuts w ↔ p.1 * p.2 = FreeMonoid.ofList w := by
  unfold wordCuts
  constructor
  · rintro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    change w.take k ++ w.drop k = w
    exact List.take_append_drop k w
  · intro h
    apply Finset.mem_image.mpr
    have hp : p.1.toList ++ p.2.toList = w := h
    refine ⟨p.1.toList.length, Finset.mem_range.mpr ?_, ?_⟩
    · rw [← hp, List.length_append]
      omega
    · apply Prod.ext <;> apply FreeMonoid.toList.injective
      · simp [← hp]
      · simp [← hp]

private theorem cuts_injective {n : ℕ} (w : Word n) :
    Set.InjOn (fun k => (FreeMonoid.ofList (w.take k), FreeMonoid.ofList (w.drop k)))
      (Finset.range (w.length + 1)) := by
  intro k hk l hl h
  have he := congrArg (fun p : FreeMonoid (Fin n) × FreeMonoid (Fin n) =>
    p.1.toList.length) h
  simp only [FreeMonoid.toList_ofList, List.length_take] at he
  have hk' : k ≤ w.length := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hl' : l ≤ w.length := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  simpa [Nat.min_eq_left hk', Nat.min_eq_left hl'] using he

theorem monoidAlgebra_coeff_mul {F : Type*} {n : ℕ} [Semiring F]
    (f g : MonoidAlgebra F (FreeMonoid (Fin n))) (w : Word n) :
    (f * g).coeff (FreeMonoid.ofList w) =
      convolution (fun v => f.coeff (FreeMonoid.ofList v))
        (fun v => g.coeff (FreeMonoid.ofList v)) w := by
  rw [MonoidAlgebra.coeff_mul_antidiag f g _ (wordCuts w) (fun {_} => mem_wordCuts w _),
    convolution_eq_sum]
  exact Finset.sum_image (cuts_injective w)

theorem sum_eq_sum_wordsOfLength {F M : Type*} {n d : ℕ}
    [Zero F] [AddCommMonoid M] (p : Word n →₀ F)
    (hcut : ∀ w, d ≤ w.length → p w = 0)
    (h : Word n → F → M) (hzero : ∀ w, h w 0 = 0) :
    p.sum h = ∑ k ∈ Finset.range d, ∑ w ∈ wordsOfLength n k, h w (p w) := by
  classical
  let S := (Finset.range d).biUnion (wordsOfLength n)
  have hsupport : p.support ⊆ S := by
    intro w hw
    have hne : p w ≠ 0 := Finsupp.mem_support_iff.mp hw
    have hlen : w.length < d := by
      by_contra hn
      exact hne (hcut w (by omega))
    exact Finset.mem_biUnion.mpr ⟨w.length, Finset.mem_range.mpr hlen,
      (mem_wordsOfLength w).mpr rfl⟩
  rw [Finsupp.sum_of_support_subset p hsupport h (fun w _ => hzero w)]
  apply Finset.sum_biUnion
  intro k hk l hl hkl
  apply Finset.disjoint_left.mpr
  intro w hwk hwl
  exact hkl (((mem_wordsOfLength w).mp hwk).symm.trans ((mem_wordsOfLength w).mp hwl))

namespace Formula

noncomputable def monoidPolynomial {F : Type*} {n : ℕ} [Semiring F] :
    Formula F n → MonoidAlgebra F (FreeMonoid (Fin n))
  | scalar a => MonoidAlgebra.single 1 a
  | var i => MonoidAlgebra.single (FreeMonoid.of i) 1
  | add f g => monoidPolynomial f + monoidPolynomial g
  | mul f g => monoidPolynomial f * monoidPolynomial g

@[simp] theorem monoidPolynomial_coeff {F : Type*} {n : ℕ} [Semiring F]
    (f : Formula F n) (w : Word n) :
    f.monoidPolynomial.coeff (FreeMonoid.ofList w) = f.coeff w := by
  classical
  induction f generalizing w with
  | scalar a =>
    simp only [monoidPolynomial, coeff, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    change (if ([] : Word n) = w then a else 0) = (if w = [] then a else 0)
    simp [eq_comm]
  | var i =>
    simp only [monoidPolynomial, coeff, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    change (if [i] = w then 1 else 0) = (if w = [i] then 1 else (0 : F))
    simp [eq_comm]
  | add f g ihf ihg => simp [monoidPolynomial, coeff, ihf, ihg]
  | mul f g ihf ihg =>
    rw [monoidPolynomial, monoidAlgebra_coeff_mul]
    simp only [ihf, ihg, coeff]

theorem eval_eq_lift {F A : Type*} {n : ℕ} [CommSemiring F] [Semiring A]
    [Algebra F A] (f : Formula F n) (T : Fin n → A) :
    f.eval (algebraMap F A) T =
      MonoidAlgebra.lift F A (FreeMonoid (Fin n)) (FreeMonoid.lift T) f.monoidPolynomial := by
  induction f with
  | scalar a => simp [eval, monoidPolynomial, Algebra.smul_def]
  | var i => simp [eval, monoidPolynomial]
  | add f g ihf ihg => simp [eval, monoidPolynomial, ihf, ihg]
  | mul f g ihf ihg => simp [eval, monoidPolynomial, ihf, ihg]

theorem eval_eq_sum {F A : Type*} {n : ℕ} [CommSemiring F] [Semiring A]
    [Algebra F A] (f : Formula F n) (T : Fin n → A) :
    f.eval (algebraMap F A) T =
      f.polynomial.sum (fun w a => algebraMap F A a * (w.map T).prod) := by
  rw [eval_eq_lift, MonoidAlgebra.lift_apply']
  have hcoeff : f.monoidPolynomial.coeff = f.polynomial := by
    ext w
    exact monoidPolynomial_coeff f w
  rw [hcoeff]
  apply Finset.sum_congr rfl
  intro w hw
  change algebraMap F A (f.coeff w) * FreeMonoid.lift T w =
    algebraMap F A (f.coeff w) * (w.toList.map T).prod
  rw [FreeMonoid.lift_apply]

theorem eval_eq_sum_of_cutoff {F A : Type*} {n d : ℕ}
    [CommSemiring F] [Semiring A] [Algebra F A]
    (f : Formula F n) (T : Fin n → A)
    (hcut : ∀ w, d ≤ w.length → f.coeff w = 0) :
    f.eval (algebraMap F A) T =
      ∑ k ∈ Finset.range d, ∑ w ∈ wordsOfLength n k,
        algebraMap F A (f.coeff w) * (w.map T).prod := by
  rw [eval_eq_sum]
  exact sum_eq_sum_wordsOfLength f.polynomial hcut _ (by intro w; simp)

theorem eval_eq_sum_wordsOfLength {F A : Type*} {n s : ℕ}
    [CommSemiring F] [Semiring A] [Algebra F A]
    (f : Formula F n) (T : Fin n → A) (hs : f.size ≤ s) :
    f.eval (algebraMap F A) T =
      ∑ k ∈ Finset.range (s + 1), ∑ w ∈ wordsOfLength n k,
        algebraMap F A (f.coeff w) * (w.map T).prod := by
  classical
  rw [eval_eq_sum]
  let S := (Finset.range (s + 1)).biUnion (wordsOfLength n)
  have hsupport : f.polynomial.support ⊆ S := by
    intro w hw
    have hne : f.coeff w ≠ 0 := Finsupp.mem_support_iff.mp hw
    have hlen : w.length ≤ s := by
      by_contra h
      exact hne (f.coeff_eq_zero_of_length_gt w (by omega))
    exact Finset.mem_biUnion.mpr ⟨w.length, Finset.mem_range.mpr (by omega),
      (mem_wordsOfLength w).mpr rfl⟩
  rw [Finsupp.sum_of_support_subset f.polynomial hsupport _ (by intros; simp)]
  change (∑ w ∈ S, algebraMap F A (f.coeff w) * (w.map T).prod) = _
  apply Finset.sum_biUnion
  intro k hk l hl hkl
  apply Finset.disjoint_left.mpr
  intro w hwk hwl
  exact hkl (((mem_wordsOfLength w).mp hwk).symm.trans ((mem_wordsOfLength w).mp hwl))

end Formula
end NCHitting

end OAI
