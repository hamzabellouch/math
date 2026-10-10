import Mathlib

namespace OAI

universe u v

noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

def scalarWeight (p : ℝ) (b : Bool) : ℝ :=
  if b = true then p else 1 - p

def weight (p : ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, scalarWeight p (x i)

def chi (p : ℝ) (b : Bool) : ℝ :=
  ((if b = true then (1 : ℝ) else 0) - p) / Real.sqrt (p * (1 - p))

def char (p : ℝ) (S : Finset ι) (x : ι → Bool) : ℝ :=
  ∏ i ∈ S, chi p (x i)

def coeff (p : ℝ) (g : (ι → Bool) → ℝ) (S : Finset ι) : ℝ := by
  classical
  exact ∑ x, weight p x * g x * char p S x

@[simp] theorem scalarWeight_false (p : ℝ) : scalarWeight p false = 1 - p := rfl
@[simp] theorem scalarWeight_true (p : ℝ) : scalarWeight p true = p := rfl
@[simp] theorem chi_false (p : ℝ) :
    chi p false = -p / Real.sqrt (p * (1 - p)) := by simp [chi]
@[simp] theorem chi_true (p : ℝ) :
    chi p true = (1 - p) / Real.sqrt (p * (1 - p)) := rfl
omit [Fintype ι] in
@[simp] theorem char_empty (p : ℝ) (x : ι → Bool) : char p ∅ x = 1 := by
  simp [char]

theorem scalar_kernel {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (b c : Bool) :
    scalarWeight p c * (1 + chi p b * chi p c) = if b = c then 1 else 0 := by
  have hpos : 0 < p * (1 - p) := mul_pos hp (sub_pos.mpr hp1)
  have hs : Real.sqrt (p * (1 - p)) ^ 2 = p * (1 - p) :=
    Real.sq_sqrt hpos.le
  have hn : Real.sqrt (p * (1 - p)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  cases b <;> cases c <;> simp only [scalarWeight, chi, Bool.false_eq_true,
    Bool.true_eq_false, ite_false, ite_true, zero_sub]
  all_goals field_simp
  all_goals nlinarith [hs]

theorem character_kernel {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x y : ι → Bool) :
    weight p y * (∑ S : Finset ι, char p S x * char p S y) =
      if x = y then 1 else 0 := by
  classical
  have hk : (∑ S : Finset ι, char p S x * char p S y) =
      ∏ i, (1 + chi p (x i) * chi p (y i)) := by
    simpa [char, Finset.prod_mul_distrib] using
      (Finset.prod_one_add (f := fun i : ι => chi p (x i) * chi p (y i))
        Finset.univ).symm
  rw [hk, weight, ← Finset.prod_mul_distrib]
  simp_rw [scalar_kernel hp hp1]
  simp [Fintype.prod_ite_zero, funext_iff]

theorem inversion {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (x : ι → Bool) :
    ∑ S : Finset ι, coeff p g S * char p S x = g x := by
  classical
  simp_rw [coeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ y, ∑ S : Finset ι, weight p y * g y * char p S y * char p S x) =
        ∑ y, g y * (weight p y * ∑ S : Finset ι, char p S x * char p S y) := by
      apply Finset.sum_congr rfl
      intro y hy
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      ring
    _ = ∑ y, g y * (if x = y then 1 else 0) := by
      simp_rw [character_kernel hp hp1]
    _ = g x := by simp

theorem parseval [DecidableEq ι] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) :
    (∑ S : Finset ι, coeff p g S ^ 2) = ∑ x, weight p x * (g x) ^ 2 := by
  classical
  calc
    (∑ S : Finset ι, coeff p g S ^ 2) =
        ∑ S : Finset ι, ∑ x, weight p x * g x * (coeff p g S * char p S x) := by
      apply Finset.sum_congr rfl
      intro S hS
      conv_lhs => rw [pow_two, coeff]
      rw [Finset.sum_mul]
      apply Finset.sum_congr (by ext; simp)
      intro x hx
      dsimp [coeff]
      ring
    _ = ∑ x, weight p x * g x * (∑ S : Finset ι, coeff p g S * char p S x) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = ∑ x, weight p x * (g x) ^ 2 := by
      simp_rw [inversion hp hp1]
      apply Finset.sum_congr rfl
      intro x hx
      ring

theorem coeff_zero (p : ℝ) (S : Finset ι) :
    coeff p (fun _ : ι → Bool => 0) S = 0 := by
  classical
  simp [coeff]

theorem coeff_add (p : ℝ) (g h : (ι → Bool) → ℝ) (S : Finset ι) :
    coeff p (fun x => g x + h x) S = coeff p g S + coeff p h S := by
  classical
  simp [coeff, mul_add, add_mul, Finset.sum_add_distrib]

theorem coeff_sub (p : ℝ) (g h : (ι → Bool) → ℝ) (S : Finset ι) :
    coeff p (fun x => g x - h x) S = coeff p g S - coeff p h S := by
  classical
  simp [coeff, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem coeff_smul (p c : ℝ) (g : (ι → Bool) → ℝ) (S : Finset ι) :
    coeff p (fun x => c * g x) S = c * coeff p g S := by
  classical
  simp only [coeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem coeff_sum {κ : Type v} (p : ℝ) (s : Finset κ)
    (g : κ → (ι → Bool) → ℝ) (S : Finset ι) :
    coeff p (fun x => ∑ j ∈ s, g j x) S = ∑ j ∈ s, coeff p (g j) S := by
  classical
  simp only [coeff, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem inner_parseval [DecidableEq ι] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g h : (ι → Bool) → ℝ) :
    (∑ S : Finset ι, coeff p g S * coeff p h S) =
      ∑ x, weight p x * g x * h x := by
  classical
  calc
    (∑ S : Finset ι, coeff p g S * coeff p h S) =
        ∑ S : Finset ι, ∑ x, weight p x * g x * (coeff p h S * char p S x) := by
      apply Finset.sum_congr rfl
      intro S hS
      conv_lhs => lhs; unfold coeff
      rw [Finset.sum_mul]
      apply Finset.sum_congr (by ext; simp)
      intro x hx
      ring
    _ = ∑ x, weight p x * g x * (∑ S : Finset ι, coeff p h S * char p S x) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = ∑ x, weight p x * g x * h x := by
      simp_rw [inversion hp hp1]

end Problem313.BiasedFourier

end

end OAI
