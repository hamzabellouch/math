import OAI.InformationTheory.BooleanNoise.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators

noncomputable section

universe u

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

@[simp] theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n :=
  LeanBlast.GotsmanLinial.card_cube n

theorem cube_denominator_pos (n : ℕ) : 0 < (2 : ℝ) ^ n := by positivity

@[simp] theorem cubeAverage_const (n : ℕ) (c : ℝ) :
    cubeAverage (fun _ : Cube n => c) = c := by
  simp [cubeAverage]

theorem cubeAverage_zeroDim (g : Cube 0 → ℝ) :
    cubeAverage g = g (fun _ => false) := by
  simp only [cubeAverage, pow_zero, div_one, Fintype.sum_unique]
  exact congrArg g (Subsingleton.elim _ _)

theorem cubeAverage_add (g h : Cube n → ℝ) :
    cubeAverage (fun x => g x + h x) = cubeAverage g + cubeAverage h := by
  simp [cubeAverage, Finset.sum_add_distrib, add_div]

theorem cubeAverage_sub (g h : Cube n → ℝ) :
    cubeAverage (fun x => g x - h x) = cubeAverage g - cubeAverage h := by
  simp [cubeAverage, Finset.sum_sub_distrib, sub_div]

theorem cubeAverage_neg (g : Cube n → ℝ) :
    cubeAverage (fun x => -g x) = -cubeAverage g := by
  simp [cubeAverage, neg_div]

theorem cubeAverage_smul (c : ℝ) (g : Cube n → ℝ) :
    cubeAverage (fun x => c * g x) = c * cubeAverage g := by
  simp [cubeAverage, ← Finset.mul_sum, mul_div_assoc]

theorem cubeAverage_sum {ι : Type u} [Fintype ι] (f : ι → Cube n → ℝ) :
    cubeAverage (fun x => ∑ i, f i x) = ∑ i, cubeAverage (f i) := by
  simp only [cubeAverage, Finset.sum_div]
  exact Finset.sum_comm

theorem cubeAverage_nonneg {g : Cube n → ℝ} (hg : ∀ x, 0 ≤ g x) :
    0 ≤ cubeAverage g :=
  div_nonneg (Finset.sum_nonneg fun x _ => hg x) (le_of_lt (cube_denominator_pos n))

theorem cubeAverage_mono {g h : Cube n → ℝ} (hgh : ∀ x, g x ≤ h x) :
    cubeAverage g ≤ cubeAverage h := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hgh x)
    (le_of_lt (cube_denominator_pos n))

theorem cubeAverage_strict_mono {g h : Cube n → ℝ} (hgh : ∀ x, g x ≤ h x)
    (hlt : ∃ x, g x < h x) : cubeAverage g < cubeAverage h := by
  apply (div_lt_div_iff_of_pos_right (cube_denominator_pos n)).2
  apply Finset.sum_lt_sum (fun x _ => hgh x)
  obtain ⟨x, hx⟩ := hlt
  exact ⟨x, Finset.mem_univ x, hx⟩

theorem cubeAverage_lt {g h : Cube n → ℝ} (hgh : ∀ x, g x < h x) :
    cubeAverage g < cubeAverage h := by
  exact cubeAverage_strict_mono (fun x => (hgh x).le) ⟨fun _ => false, hgh _⟩

theorem IsInterior.cubeAverage {g : Cube n → ℝ} (hg : IsInterior g) :
    -1 < cubeAverage g ∧ cubeAverage g < 1 := by
  constructor
  · simpa using cubeAverage_lt (fun x => (hg x).1)
  · simpa using cubeAverage_lt (fun x => (hg x).2)

theorem cubeAverage_le_const {g : Cube n → ℝ} {c : ℝ} (hg : ∀ x, g x ≤ c) :
    cubeAverage g ≤ c := by
  simpa using cubeAverage_mono hg

theorem const_le_cubeAverage {g : Cube n → ℝ} {c : ℝ} (hg : ∀ x, c ≤ g x) :
    c ≤ cubeAverage g := by
  simpa using cubeAverage_mono hg

theorem noiseKernel_symm (u : ℝ) (x y : Cube n) :
    noiseKernel u x y = noiseKernel u y x := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : x i = y i
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem noiseKernel_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (x y : Cube n) : 0 ≤ noiseKernel u x y := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

theorem noiseKernel_pos {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (x y : Cube n) : 0 < noiseKernel u x y := by
  apply Finset.prod_pos
  intro i _
  split_ifs <;> linarith

theorem noiseKernel_row_sum (u : ℝ) (x : Cube n) :
    ∑ y, noiseKernel u x y = 1 := by
  unfold noiseKernel
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    if x i = b then (1 + u) / 2 else (1 - u) / 2)]
  have hfactor : ∀ i : Fin n,
      (∑ b : Bool, if x i = b then (1 + u) / 2 else (1 - u) / 2) = 1 := by
    intro i
    cases x i <;> simp <;> ring
  simp_rw [hfactor]
  simp

theorem noiseKernel_col_sum (u : ℝ) (y : Cube n) :
    ∑ x, noiseKernel u x y = 1 := by
  simp_rw [noiseKernel_symm u]
  exact noiseKernel_row_sum u y

theorem noiseKernel_split_coord (u : ℝ) (x y : Cube n) (i : Fin n) :
    noiseKernel u x y =
      (if x i = y i then (1 + u) / 2 else (1 - u) / 2) *
        ∏ j ∈ Finset.univ.erase i, if x j = y j then (1 + u) / 2 else (1 - u) / 2 := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

@[simp] theorem noiseOperator_const (u c : ℝ) (x : Cube n) :
    noiseOperator u (fun _ => c) x = c := by
  rw [noiseOperator, ← Finset.sum_mul, noiseKernel_row_sum, one_mul]

theorem noiseOperator_add (u : ℝ) (g h : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => g y + h y) x = noiseOperator u g x + noiseOperator u h x := by
  simp [noiseOperator, mul_add, Finset.sum_add_distrib]

theorem noiseOperator_sub (u : ℝ) (g h : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => g y - h y) x = noiseOperator u g x - noiseOperator u h x := by
  simp [noiseOperator, mul_sub, Finset.sum_sub_distrib]

theorem noiseOperator_neg (u : ℝ) (g : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => -g y) x = -noiseOperator u g x := by
  simp [noiseOperator]

theorem noiseOperator_smul (u c : ℝ) (g : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => c * g y) x = c * noiseOperator u g x := by
  simp [noiseOperator, Finset.mul_sum, mul_left_comm]

theorem cubeAverage_noiseOperator (u : ℝ) (g : Cube n → ℝ) :
    cubeAverage (noiseOperator u g) = cubeAverage g := by
  unfold cubeAverage noiseOperator
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, noiseKernel_col_sum, one_mul]

theorem noiseOperator_prod (u : ℝ) (f : Fin n → Bool → ℝ) (x : Cube n) :
    noiseOperator u (fun y => ∏ i, f i (y i)) x =
      ∏ i, ∑ b : Bool, (if x i = b then (1 + u) / 2 else (1 - u) / 2) * f i b := by
  unfold noiseOperator noiseKernel
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    (if x i = b then (1 + u) / 2 else (1 - u) / 2) * f i b)).symm

@[simp] theorem noiseKernel_zero (x y : Cube n) :
    noiseKernel 0 x y = 1 / (2 : ℝ) ^ n := by
  simp [noiseKernel, one_div]

@[simp] theorem noiseOperator_zero_correlation (g : Cube n → ℝ) (x : Cube n) :
    noiseOperator 0 g x = cubeAverage g := by
  simp only [noiseOperator, noiseKernel_zero, ← Finset.mul_sum]
  unfold cubeAverage
  ring

@[simp] theorem noiseKernel_one (x y : Cube n) :
    noiseKernel 1 x y = if x = y then 1 else 0 := by
  simp only [noiseKernel, add_self_div_two, sub_self, zero_div]
  rw [Fintype.prod_boole]
  simp only [← funext_iff]

@[simp] theorem noiseOperator_one (g : Cube n → ℝ) (x : Cube n) :
    noiseOperator 1 g x = g x := by
  simp [noiseOperator]

theorem noiseOperator_mono {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {g h : Cube n → ℝ} (hgh : ∀ y, g y ≤ h y) (x : Cube n) :
    noiseOperator u g x ≤ noiseOperator u h x := by
  exact Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_left (hgh y) (noiseKernel_nonneg hu0 hu1 x y)

theorem noiseOperator_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {g : Cube n → ℝ} (hg : ∀ y, -1 ≤ g y ∧ g y ≤ 1) (x : Cube n) :
    -1 ≤ noiseOperator u g x ∧ noiseOperator u g x ≤ 1 := by
  constructor
  · simpa using noiseOperator_mono hu0 hu1 (fun y => (hg y).1) x
  · simpa using noiseOperator_mono hu0 hu1 (fun y => (hg y).2) x

theorem noiseOperator_strict_mono {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {g h : Cube n → ℝ} (hgh : ∀ y, g y ≤ h y) (hlt : ∃ y, g y < h y) (x : Cube n) :
    noiseOperator u g x < noiseOperator u h x := by
  apply Finset.sum_lt_sum
  · intro y _
    exact mul_le_mul_of_nonneg_left (hgh y) (le_of_lt (noiseKernel_pos hu0 hu1 x y))
  · obtain ⟨y, hy⟩ := hlt
    exact ⟨y, Finset.mem_univ y, mul_lt_mul_of_pos_left hy (noiseKernel_pos hu0 hu1 x y)⟩

theorem exists_signs_of_nonconstant {g : Cube n → ℝ} (hg : IsSignValued g)
    (hne : ∃ x y, g x ≠ g y) : (∃ x, g x = 1) ∧ (∃ y, g y = -1) := by
  obtain ⟨x, y, hxy⟩ := hne
  rcases hg x with hx | hx <;> rcases hg y with hy | hy
  · exact False.elim (hxy (hx.trans hy.symm))
  · exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · exact ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
  · exact False.elim (hxy (hx.trans hy.symm))

theorem noiseOperator_isInterior_of_exists_signs {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {g : Cube n → ℝ} (hg : IsSignValued g)
    (hpos : ∃ x, g x = 1) (hneg : ∃ y, g y = -1) :
    IsInterior (noiseOperator u g) := by
  have hb : ∀ y, -1 ≤ g y ∧ g y ≤ 1 := by
    intro y
    rcases hg y with h | h <;> rw [h] <;> norm_num
  intro x
  constructor
  · have hs : ∃ y, (-1 : ℝ) < g y := by
      obtain ⟨y, hy⟩ := hpos
      exact ⟨y, by rw [hy]; norm_num⟩
    simpa using noiseOperator_strict_mono hu0 hu1 (fun y => (hb y).1) hs x
  · have hs : ∃ y, g y < (1 : ℝ) := by
      obtain ⟨y, hy⟩ := hneg
      exact ⟨y, by rw [hy]; norm_num⟩
    simpa using noiseOperator_strict_mono hu0 hu1 (fun y => (hb y).2) hs x

theorem noiseOperator_isInterior {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {g : Cube n → ℝ} (hg : IsSignValued g) (hne : ∃ x y, g x ≠ g y) :
    IsInterior (noiseOperator u g) := by
  obtain ⟨hp, hn⟩ := exists_signs_of_nonconstant hg hne
  exact noiseOperator_isInterior_of_exists_signs hu0 hu1 hg hp hn

theorem cubeAverage_mem_Ioo_of_signValued_nonconstant {g : Cube n → ℝ}
    (hg : IsSignValued g) (hne : ∃ x y, g x ≠ g y) :
    -1 < cubeAverage g ∧ cubeAverage g < 1 := by
  simpa using noiseOperator_isInterior (u := 0) (by norm_num) (by norm_num) hg hne
    (fun _ => false)

theorem meanVariance_pos_of_signValued_nonconstant {g : Cube n → ℝ}
    (hg : IsSignValued g) (hne : ∃ x y, g x ≠ g y) : 0 < meanVariance g := by
  obtain ⟨hlo, hhi⟩ := cubeAverage_mem_Ioo_of_signValued_nonconstant hg hne
  unfold meanVariance
  nlinarith [sq_nonneg (cubeAverage g), mul_pos (by linarith : 0 < 1 - cubeAverage g)
    (by linarith : 0 < 1 + cubeAverage g)]

end LeanBlast.CourtadeKumar

end

end OAI
