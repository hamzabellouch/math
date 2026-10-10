import OAI.NumberTheory.JointDickman.Amplification.FiniteHoeffding

namespace OAI

/-! # Exponential moments under finite independent coordinate laws -/
namespace JointDickman
open Finset PublishedInputs

theorem hammingDist_cons {A : Type*} [DecidableEq A] {n : ℕ}
    (a b : A) (x y : Fin n → A) :
    hammingDist (Fin.cons a x : Fin (n+1) → A) (Fin.cons b y : Fin (n+1) → A) =
      (if a = b then 0 else 1) + hammingDist x y := by
  classical
  simp only [hammingDist,card_eq_sum_ones,sum_filter,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ]
  by_cases hab : a = b <;> simp [hab]

theorem siteProductMass_cons {A : Type*} {n : ℕ} (p : Fin (n+1) → A → ℝ)
    (a : A) (x : Fin n → A) :
    siteProductMass p (Fin.cons a x) =
      p 0 a * siteProductMass (fun i => p i.succ) x := by
  simp [siteProductMass,Fin.prod_univ_succ]

theorem finite_product_expectation_cons {A : Type*} [Fintype A] {n : ℕ}
    (p : Fin (n+1) → A → ℝ) (f : (Fin (n+1) → A) → ℝ) :
    finiteExpectation (siteProductMass p) f =
      finiteExpectation (siteProductMass (fun i => p i.succ))
        (fun x => finiteExpectation (p 0) (fun a => f (Fin.cons a x))) := by
  classical
  unfold finiteExpectation
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  change siteProductMass p (Fin.cons a x) * f (Fin.cons a x) = _
  rw [siteProductMass_cons]
  ring

theorem finiteExpectation_sub_le {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hone : ∑ a, p a = 1)
    (f g : A → ℝ) {c : ℝ} (hfg : ∀ a, |f a-g a| ≤ c) :
    |finiteExpectation p f - finiteExpectation p g| ≤ c := by
  calc
    _ = |∑ a, p a * (f a-g a)| := by
      simp only [finiteExpectation,mul_sub,sum_sub_distrib]
    _ ≤ ∑ a, p a * |f a-g a| := by
      simpa only [abs_mul,abs_of_nonneg (hp _)] using
        (abs_sum_le_sum_abs (fun a => p a * (f a-g a)) univ)
    _ ≤ ∑ a, p a * c := sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hfg a) (hp a))
    _ = c := by rw [← sum_mul,hone,one_mul]

theorem siteProductMass_sum_one {A : Type*} [Fintype A] (n : ℕ)
    (p : Fin n → A → ℝ) (hone : ∀ i, ∑ a, p i a = 1) :
    ∑ x, siteProductMass p x = 1 := by
  induction n with
  | zero => simp [siteProductMass]
  | succ n ih =>
    have h := finite_product_expectation_cons p (fun _ => 1)
    simp only [finiteExpectation,mul_one,hone] at h
    rw [h]
    exact ih (fun i => p i.succ) (fun i => hone i.succ)

theorem finite_product_mgf {A : Type*} [Fintype A] [DecidableEq A]
    (n : ℕ) (p : Fin n → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hone : ∀ i, ∑ a, p i a = 1) (f : (Fin n → A) → ℝ)
    {c : ℝ} (hc : 0 ≤ c)
    (hlip : ∀ x y, |f x-f y| ≤ c * hammingDist x y) (t : ℝ) :
    finiteExpectation (siteProductMass p)
      (fun x => Real.exp (t * (f x-finiteExpectation (siteProductMass p) f))) ≤
        Real.exp ((n : ℝ)*c^2*t^2/8) := by
  classical
  induction n with
  | zero => simp [finiteExpectation,siteProductMass]
  | succ n ih =>
    let q : Fin n → A → ℝ := fun i => p i.succ
    let g : (Fin n → A) → ℝ := fun x => finiteExpectation (p 0) (fun a => f (Fin.cons a x))
    have hmean : finiteExpectation (siteProductMass p) f =
        finiteExpectation (siteProductMass q) g := finite_product_expectation_cons p f
    have hg : ∀ x y, |g x-g y| ≤ c * hammingDist x y := by
      intro x y
      apply finiteExpectation_sub_le (p 0) (hp 0) (hone 0)
      intro a
      simpa [hammingDist_cons] using
        hlip (Fin.cons a x) (Fin.cons a y)
    have hcond (x : Fin n → A) :
        finiteExpectation (p 0) (fun a => Real.exp (t * (f (Fin.cons a x)-g x))) ≤
          Real.exp (c^2*t^2/8) := by
      apply finite_hoeffding_diameter (p 0) (hp 0) (hone 0)
      intro a b
      have hh := hlip (Fin.cons a x) (Fin.cons b x)
      rw [hammingDist_cons,hammingDist_self,add_zero] at hh
      split_ifs at hh with hab
      · simp only [Nat.cast_zero,mul_zero] at hh
        exact hh.trans hc
      · simpa only [Nat.cast_one,mul_one] using hh
    have hstep (x : Fin n → A) :
        finiteExpectation (p 0)
          (fun a => Real.exp (t * (f (Fin.cons a x)-finiteExpectation (siteProductMass q) g))) ≤
        Real.exp (t * (g x-finiteExpectation (siteProductMass q) g)) *
          Real.exp (c^2*t^2/8) := by
      calc
        _ = Real.exp (t * (g x-finiteExpectation (siteProductMass q) g)) *
            finiteExpectation (p 0) (fun a => Real.exp (t * (f (Fin.cons a x)-g x))) := by
          change (∑ a, p 0 a * Real.exp (t * (f (Fin.cons a x)-finiteExpectation (siteProductMass q) g))) =
            Real.exp (t * (g x-finiteExpectation (siteProductMass q) g)) *
              ∑ a, p 0 a * Real.exp (t * (f (Fin.cons a x)-g x))
          rw [mul_sum]
          apply sum_congr rfl
          intro a _
          rw [show t * (f (Fin.cons a x)-finiteExpectation (siteProductMass q) g) =
            t * (g x-finiteExpectation (siteProductMass q) g) + t * (f (Fin.cons a x)-g x) by ring]
          rw [Real.exp_add]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcond x) (Real.exp_pos _).le
    rw [hmean,finite_product_expectation_cons]
    calc
      _ ≤ finiteExpectation (siteProductMass q)
          (fun x => Real.exp (t * (g x-finiteExpectation (siteProductMass q) g)) *
            Real.exp (c^2*t^2/8)) :=
        sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hstep x)
          (prod_nonneg (fun i _ => hp i.succ (x i))))
      _ = finiteExpectation (siteProductMass q)
          (fun x => Real.exp (t * (g x-finiteExpectation (siteProductMass q) g))) *
            Real.exp (c^2*t^2/8) := by simp only [finiteExpectation,← mul_assoc,sum_mul]
      _ ≤ Real.exp ((n : ℝ)*c^2*t^2/8) * Real.exp (c^2*t^2/8) :=
        mul_le_mul_of_nonneg_right
          (ih q (fun i => hp i.succ) (fun i => hone i.succ) g hg)
          (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

end JointDickman

end OAI
