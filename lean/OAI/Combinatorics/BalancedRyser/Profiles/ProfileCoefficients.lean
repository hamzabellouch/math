import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

open scoped BigOperators

namespace Balanced.ProfileCoefficients

variable {α : Type*}

theorem summable_abs_shift_sub (x P : α → ℝ) (hx : Summable x) (hP : Summable P)
    (shift : α → α) (hinj : Function.Injective shift) :
    Summable (fun a => |x (shift a) - P a|) :=
  ((hx.comp_injective hinj).sub hP).abs

theorem tsum_abs_shift_sub_le_two (x P : α → ℝ)
    (hx0 : ∀ a, 0 ≤ x a) (hP0 : ∀ a, 0 ≤ P a)
    (hx : HasSum x 1) (hP : HasSum P 1)
    (shift : α → α) (hinj : Function.Injective shift) :
    (∑' a, |x (shift a) - P a|) ≤ 2 := by
  have hxs := hx.summable.comp_injective hinj
  have hbound : ∀ a, |x (shift a) - P a| ≤ x (shift a) + P a := by
    intro a
    calc
      _ ≤ |x (shift a)| + |P a| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg (hx0 _), abs_of_nonneg (hP0 _)]
  have hmass : (∑' a, x (shift a)) ≤ 1 := by
    rw [← hx.tsum_eq]
    exact hxs.tsum_le_tsum_of_inj shift hinj (fun a _ => hx0 a) (fun _ => le_rfl) hx.summable
  calc
    _ ≤ ∑' a, (x (shift a) + P a) :=
      (summable_abs_shift_sub x P hx.summable hP.summable shift hinj).tsum_le_tsum
        hbound (hxs.add hP.summable)
    _ = (∑' a, x (shift a)) + ∑' a, P a := hxs.tsum_add hP.summable
    _ ≤ 2 := by rw [hP.tsum_eq]; linarith

theorem summable_mul_weight (x w : α → ℝ) (hx : Summable x)
    (hw : ∀ a, |w a| ≤ 1) : Summable (fun a => x a * w a) := by
  apply hx.abs.of_norm_bounded
  intro a
  rw [Real.norm_eq_abs, abs_mul]
  simpa using mul_le_mul_of_nonneg_left (hw a) (abs_nonneg (x a))

theorem shifted_transform_sub (x P w : α → ℝ) (hx : Summable x) (hP : Summable P)
    (shift : α → α) (hinj : Function.Injective shift) (hw : ∀ a, |w a| ≤ 1) :
    (∑' a, x (shift a) * w a) - (∑' a, P a * w a) =
      ∑' a, (x (shift a) - P a) * w a := by
  have hsum := (summable_mul_weight (x ∘ shift) w (hx.comp_injective hinj) hw).tsum_sub
      (summable_mul_weight P w hP hw)
  simp only [Function.comp_apply] at hsum
  rw [← hsum]
  apply tsum_congr
  intro a
  ring

theorem shift_fst_injective :
    Function.Injective (fun a : ℕ × ℕ => (a.1 + 1, a.2)) := by
  intro a b h
  apply Prod.ext
  · exact Nat.add_right_cancel (congrArg Prod.fst h)
  · simpa only using congrArg (fun p : ℕ × ℕ => p.2) h

theorem shift_snd_injective :
    Function.Injective (fun a : ℕ × ℕ => (a.1, a.2 + 1)) := by
  intro a b h
  apply Prod.ext
  · simpa only using congrArg (fun p : ℕ × ℕ => p.1) h
  · exact Nat.add_right_cancel (congrArg Prod.snd h)

theorem d_invisibility_iff (x P : ℕ × ℕ → ℝ) :
    (∀ i j, x (i, j) = if i = 0 then 0 else P (i - 1, j)) ↔
      (∀ j, x (0, j) = 0) ∧ (∀ a : ℕ × ℕ, x (a.1 + 1, a.2) - P a = 0) := by
  constructor
  · intro h
    constructor
    · intro j
      simpa using h 0 j
    · rintro ⟨i, j⟩
      simpa only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel, sub_eq_zero] using h (i + 1) j
  · rintro ⟨hzero, hcoeff⟩ i j
    cases i with
    | zero => simpa using hzero j
    | succ i => simpa only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one,
        Nat.succ_eq_add_one, sub_eq_zero] using hcoeff (i, j)

theorem c_invisibility_iff (x P : ℕ × ℕ → ℝ) :
    (∀ i j, x (i, j) = if j = 0 then 0 else P (i, j - 1)) ↔
      (∀ i, x (i, 0) = 0) ∧ (∀ a : ℕ × ℕ, x (a.1, a.2 + 1) - P a = 0) := by
  constructor
  · intro h
    constructor
    · intro i
      simpa using h i 0
    · rintro ⟨i, j⟩
      simpa only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel, sub_eq_zero] using h i (j + 1)
  · rintro ⟨hzero, hcoeff⟩ i j
    cases j with
    | zero => simpa using hzero i
    | succ j => simpa only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one,
        Nat.succ_eq_add_one, sub_eq_zero] using hcoeff (i, j)

theorem rpow_weight_abs_le_one {γ z : ℝ} (hγ : 0 ≤ γ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (a : ℕ × ℕ) : |z ^ ((a.1 : ℝ) + γ * a.2)| ≤ 1 := by
  rw [abs_of_nonneg (Real.rpow_nonneg hz0 _)]
  exact Real.rpow_le_one hz0 hz1 (by positivity)

theorem d_transform_sub (x P : ℕ × ℕ → ℝ) (hx : Summable x) (hP : Summable P)
    {γ z : ℝ} (hγ : 0 ≤ γ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (∑' a : ℕ × ℕ, x (a.1 + 1, a.2) * z ^ ((a.1 : ℝ) + γ * a.2)) -
      (∑' a : ℕ × ℕ, P a * z ^ ((a.1 : ℝ) + γ * a.2)) =
      ∑' a : ℕ × ℕ, (x (a.1 + 1, a.2) - P a) * z ^ ((a.1 : ℝ) + γ * a.2) :=
  shifted_transform_sub x P _ hx hP _ shift_fst_injective (rpow_weight_abs_le_one hγ hz0 hz1)

theorem c_transform_sub (x P : ℕ × ℕ → ℝ) (hx : Summable x) (hP : Summable P)
    {γ z : ℝ} (hγ : 0 ≤ γ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (∑' a : ℕ × ℕ, x (a.1, a.2 + 1) * z ^ ((a.1 : ℝ) + γ * a.2)) -
      (∑' a : ℕ × ℕ, P a * z ^ ((a.1 : ℝ) + γ * a.2)) =
      ∑' a : ℕ × ℕ, (x (a.1, a.2 + 1) - P a) * z ^ ((a.1 : ℝ) + γ * a.2) :=
  shifted_transform_sub x P _ hx hP _ shift_snd_injective (rpow_weight_abs_le_one hγ hz0 hz1)

theorem tsum_shift_fst (f : ℕ × ℕ → ℝ) (hzero : ∀ j, f (0, j) = 0) :
    (∑' a : ℕ × ℕ, f (a.1 + 1, a.2)) = ∑' a, f a := by
  apply shift_fst_injective.tsum_eq
  rintro ⟨i, j⟩ hi
  cases i with
  | zero => exact (hi (hzero j)).elim
  | succ i => exact ⟨(i, j), rfl⟩

theorem tsum_shift_snd (f : ℕ × ℕ → ℝ) (hzero : ∀ i, f (i, 0) = 0) :
    (∑' a : ℕ × ℕ, f (a.1, a.2 + 1)) = ∑' a, f a := by
  apply shift_snd_injective.tsum_eq
  rintro ⟨i, j⟩ hj
  cases j with
  | zero => exact (hj (hzero i)).elim
  | succ j => exact ⟨(i, j), rfl⟩

theorem d_transform_reindex (x : ℕ × ℕ → ℝ) (hzero : ∀ j, x (0, j) = 0)
    (γ z : ℝ) :
    (∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) - 1 + γ * a.2)) =
      ∑' a : ℕ × ℕ, x (a.1 + 1, a.2) * z ^ ((a.1 : ℝ) + γ * a.2) := by
  calc
    _ = ∑' a : ℕ × ℕ,
        x (a.1 + 1, a.2) * z ^ (((a.1 + 1 : ℕ) : ℝ) - 1 + γ * a.2) := by
      exact (tsum_shift_fst (fun a => x a * z ^ ((a.1 : ℝ) - 1 + γ * a.2))
        (fun j => by simp [hzero j])).symm
    _ = _ := by simp

theorem c_transform_reindex (x : ℕ × ℕ → ℝ) (hzero : ∀ i, x (i, 0) = 0)
    (γ z : ℝ) :
    (∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) + γ * ((a.2 : ℝ) - 1))) =
      ∑' a : ℕ × ℕ, x (a.1, a.2 + 1) * z ^ ((a.1 : ℝ) + γ * a.2) := by
  calc
    _ = ∑' a : ℕ × ℕ,
        x (a.1, a.2 + 1) * z ^ ((a.1 : ℝ) + γ * (((a.2 + 1 : ℕ) : ℝ) - 1)) := by
      exact (tsum_shift_snd (fun a => x a * z ^ ((a.1 : ℝ) + γ * ((a.2 : ℝ) - 1)))
        (fun i => by simp [hzero i])).symm
    _ = _ := by simp

theorem original_d_transform_sub (x P : ℕ × ℕ → ℝ) (hx : Summable x) (hP : Summable P)
    (hzero : ∀ j, x (0, j) = 0)
    {γ z : ℝ} (hγ : 0 ≤ γ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) - 1 + γ * a.2)) -
      (∑' a : ℕ × ℕ, P a * z ^ ((a.1 : ℝ) + γ * a.2)) =
      ∑' a : ℕ × ℕ, (x (a.1 + 1, a.2) - P a) * z ^ ((a.1 : ℝ) + γ * a.2) := by
  rw [d_transform_reindex x hzero]
  exact d_transform_sub x P hx hP hγ hz0 hz1

theorem original_c_transform_sub (x P : ℕ × ℕ → ℝ) (hx : Summable x) (hP : Summable P)
    (hzero : ∀ i, x (i, 0) = 0)
    {γ z : ℝ} (hγ : 0 ≤ γ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) + γ * ((a.2 : ℝ) - 1))) -
      (∑' a : ℕ × ℕ, P a * z ^ ((a.1 : ℝ) + γ * a.2)) =
      ∑' a : ℕ × ℕ, (x (a.1, a.2 + 1) - P a) * z ^ ((a.1 : ℝ) + γ * a.2) := by
  rw [c_transform_reindex x hzero]
  exact c_transform_sub x P hx hP hγ hz0 hz1

end Balanced.ProfileCoefficients

end OAI
