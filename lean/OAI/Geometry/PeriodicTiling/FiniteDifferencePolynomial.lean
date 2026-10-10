import OAI.Geometry.PeriodicTiling.ForwardDifference
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.Topology.Instances.AddCircle.Defs

namespace OAI

universe uA

noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

section AddCommGroup

variable {A : Type uA} [AddCommGroup A]

theorem intSequence_eq_of_forwardDiff_eq {f g : ℤ → A}
    (hd : forwardDiff f = forwardDiff g) (hzero : f 0 = g 0) : f = g := by
  have hsucc (n : ℤ) (hn : f n = g n) : f (n + 1) = g (n + 1) := by
    have h := congrFun hd n
    change f (n + 1) - f n = g (n + 1) - g n at h
    rw [hn] at h
    exact sub_left_inj.mp h
  have hpred (n : ℤ) (hn : f n = g n) : f (n - 1) = g (n - 1) := by
    have h := congrFun hd (n - 1)
    change f (n - 1 + 1) - f (n - 1) = g (n - 1 + 1) - g (n - 1) at h
    rw [sub_add_cancel, hn] at h
    exact sub_right_inj.mp h
  funext n
  refine Int.induction_on n hzero ?_ ?_
  · intro m hm
    exact hsucc (m : ℤ) hm
  · intro m hm
    exact hpred (-(m : ℤ)) hm

def newtonSequence {k : ℕ} (c : Fin k → A) (n : ℤ) : A :=
  ∑ i : Fin k, Ring.choose n i.val • c i

theorem newtonSequence_cons {k : ℕ} (a : A) (c : Fin k → A) (n : ℤ) :
    newtonSequence (Fin.cons a c) n =
      a + ∑ i : Fin k, Ring.choose n (i.val + 1) • c i := by
  rw [newtonSequence, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Ring.choose_zero_right, one_zsmul,
    Fin.cons_zero, Fin.val_succ, Fin.cons_succ]

@[simp] theorem newtonSequence_cons_zero {k : ℕ} (a : A) (c : Fin k → A) :
    newtonSequence (Fin.cons a c) 0 = a := by
  simp [newtonSequence_cons]

theorem forwardDiff_newtonSequence_cons {k : ℕ} (a : A) (c : Fin k → A) :
    forwardDiff (newtonSequence (Fin.cons a c)) = newtonSequence c := by
  funext n
  simp only [forwardDiff_apply, newtonSequence_cons]
  unfold newtonSequence
  calc
    (a + ∑ i : Fin k, Ring.choose (n + 1) (i.val + 1) • c i) -
        (a + ∑ i : Fin k, Ring.choose n (i.val + 1) • c i) =
        ∑ i : Fin k,
          (Ring.choose (n + 1) (i.val + 1) • c i -
            Ring.choose n (i.val + 1) • c i) := by
      rw [Finset.sum_sub_distrib]
      abel
    _ = ∑ i : Fin k, Ring.choose n i.val • c i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Ring.choose_succ_succ, add_zsmul, add_sub_cancel_right]

theorem exists_newtonSequence_of_iter_forwardDiff_eq_zero
    (k : ℕ) (f : ℤ → A) (hk : (forwardDiff^[k]) f = 0) :
    ∃ c : Fin k → A, f = newtonSequence c := by
  induction k generalizing f with
  | zero =>
      have hf : f = 0 := by simpa using hk
      refine ⟨Fin.elim0, ?_⟩
      subst f
      funext n
      simp [newtonSequence]
  | succ k ih =>
      have hdiff : (forwardDiff^[k]) (forwardDiff f) = 0 := by
        simpa only [Function.iterate_succ_apply] using hk
      obtain ⟨c, hc⟩ := ih (forwardDiff f) hdiff
      refine ⟨Fin.cons (f 0) c, intSequence_eq_of_forwardDiff_eq ?_ ?_⟩
      · rw [forwardDiff_newtonSequence_cons]
        exact hc
      · simp

end AddCommGroup

def newtonBasisPolynomial (k : ℕ) : Polynomial ℝ :=
  Polynomial.C ((k.factorial : ℝ)⁻¹) * descPochhammer ℝ k

theorem descPochhammer_eval_int_eq_factorial_mul_choose (k : ℕ) (n : ℤ) :
    (descPochhammer ℝ k).eval (n : ℝ) =
      (k.factorial : ℝ) * ((Ring.choose n k : ℤ) : ℝ) := by
  have h : (descPochhammer ℤ k).eval n = (k.factorial : ℤ) * Ring.choose n k := by
    simpa only [Polynomial.eval_eq_smeval, nsmul_eq_mul] using
      (Ring.descPochhammer_eq_factorial_smul_choose n k)
  rw [← descPochhammer_eval_cast ℝ k n, h, Int.cast_mul, Int.cast_natCast]

@[simp] theorem newtonBasisPolynomial_eval_int (k : ℕ) (n : ℤ) :
    (newtonBasisPolynomial k).eval (n : ℝ) = ((Ring.choose n k : ℤ) : ℝ) := by
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [newtonBasisPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    descPochhammer_eval_int_eq_factorial_mul_choose, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]

def newtonPolynomial {k : ℕ} (c : Fin k → ℝ) : Polynomial ℝ :=
  ∑ i : Fin k, Polynomial.C (c i) * newtonBasisPolynomial i.val

theorem newtonPolynomial_eval_int {k : ℕ} (c : Fin k → ℝ) (n : ℤ) :
    (newtonPolynomial c).eval (n : ℝ) =
      ∑ i : Fin k, Ring.choose n i.val • c i := by
  rw [newtonPolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    newtonBasisPolynomial_eval_int, zsmul_eq_mul]
  exact mul_comm (c i) ((Ring.choose n i.val : ℤ) : ℝ)

theorem exists_polynomial_lift_of_iter_forwardDiff_eq_zero
    (f : ℤ → AddCircle (1 : ℝ)) (k : ℕ) (hk : (forwardDiff^[k]) f = 0) :
    ∃ P : Polynomial ℝ, ∀ n : ℤ, ((P.eval (n : ℝ) : ℝ) : AddCircle (1 : ℝ)) = f n := by
  obtain ⟨c, hc⟩ := exists_newtonSequence_of_iter_forwardDiff_eq_zero k f hk
  have hrepr : ∀ i : Fin k, ∃ x : ℝ, (x : AddCircle (1 : ℝ)) = c i := by
    intro i
    exact QuotientAddGroup.mk_surjective (c i)
  choose a ha using hrepr
  refine ⟨newtonPolynomial a, ?_⟩
  intro n
  change QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
    ((newtonPolynomial a).eval (n : ℝ)) = f n
  rw [newtonPolynomial_eval_int, map_sum, hc]
  simp only [newtonSequence, map_zsmul, QuotientAddGroup.mk'_apply, ha]

end PeriodicTilingThree

end

end OAI
