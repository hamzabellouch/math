import Mathlib
import OAI.Probability.SKGap.Terminal.GibbsExpectation

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
namespace SKGapCutoff

noncomputable def cubeWeight {n : ℕ} (z : Fin n → ℝ) (x : Spin n) : ℝ :=
  ∏ i, (1 + spin x i * z i) / 2

noncomputable def deletedWeight {n : ℕ} (z : Fin n → ℝ) (x : Spin n)
    (i : Fin n) : ℝ := ∏ j ∈ Finset.univ.erase i, (1 + spin x j * z j) / 2

noncomputable def cubeExtension {n : ℕ} (f : Observables n) (z : Fin n → ℝ) : ℝ :=
  ∑ x, cubeWeight z x * f x

lemma cubeWeight_sum {n : ℕ} (z : Fin n → ℝ) : ∑ x, cubeWeight z x = 1 := by
  change (∑ x : Fin n → Bool, ∏ i, (1 + (if x i then 1 else -1 : ℝ) * z i) / 2) = 1
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    (1 + (if b then 1 else -1 : ℝ) * z i) / 2)]
  have h (i : Fin n) : (∑ b : Bool, (1 + (if b then 1 else -1 : ℝ) * z i) / 2) = 1 := by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    ring
  simp_rw [h]
  simp

lemma cubeWeight_nonneg {n : ℕ} (z : Fin n → ℝ)
    (hz : ∀ i, -1 ≤ z i ∧ z i ≤ 1) (x : Spin n) : 0 ≤ cubeWeight z x := by
  apply Finset.prod_nonneg
  intro i _
  apply div_nonneg _ (by norm_num)
  rcases hz i with ⟨hl, hu⟩
  cases h : x i <;> simp only [spin, h, ↓reduceIte, Bool.false_eq_true]
  · linarith
  · linarith

lemma cubeWeight_vertex {n : ℕ} (x y : Spin n) :
    cubeWeight (spin x) y = if y = x then 1 else 0 := by
  classical
  by_cases h : y = x
  · subst y
    simp [cubeWeight, ← sq, spin_sq]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have hs : spin y i * spin x i = -1 := by
      cases hx : x i <;> cases hy : y i <;> simp_all [spin]
    simp [hs]

lemma cubeExtension_vertex {n : ℕ} (f : Observables n) (x : Spin n) :
    cubeExtension f (spin x) = f x := by
  classical
  simp [cubeExtension, cubeWeight_vertex]

lemma deletedWeight_flip {n : ℕ} (z : Fin n → ℝ) (x : Spin n) (i : Fin n) :
    deletedWeight z (flip x i) i = deletedWeight z x i := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_erase] at hj
  rw [spin_flip]
  simp [hj.1]

lemma cubeWeight_factor {n : ℕ} (z : Fin n → ℝ) (x : Spin n) (i : Fin n) :
    cubeWeight z x = (1 + spin x i * z i) / 2 * deletedWeight z x i := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

lemma cubeWeight_flip_add {n : ℕ} (z : Fin n → ℝ) (x : Spin n) (i : Fin n) :
    cubeWeight z x + cubeWeight z (flip x i) = deletedWeight z x i := by
  rw [cubeWeight_factor z x i, cubeWeight_factor z (flip x i) i,
    deletedWeight_flip, spin_flip_self]
  ring

lemma cubeWeight_halfDiff {n : ℕ} (z : Fin n → ℝ) (f : Observables n) (i : Fin n) :
    (∑ x, cubeWeight z x * halfDiff i f x) =
      ∑ x, f x * (spin x i / 2) * deletedWeight z x i := by
  have hA (x : Spin n) :
      f x * (spin x i / 2) * deletedWeight z x i +
        f (flip x i) * (spin (flip x i) i / 2) * deletedWeight z (flip x i) i =
      deletedWeight z x i * halfDiff i f x := by
    rw [spin_flip_self, deletedWeight_flip]
    have he : f (flip x i) = f x - 2 * spin x i * halfDiff i f x := by
      linarith only [flip_sub i f x]
    rw [he]
    calc
      _ = (spin x i * spin x i) * (deletedWeight z x i * halfDiff i f x) := by ring
      _ = _ := by rw [spin_mul_self, one_mul]
  have hB (x : Spin n) :
      cubeWeight z x * halfDiff i f x +
        cubeWeight z (flip x i) * halfDiff i f (flip x i) =
      deletedWeight z x i * halfDiff i f x := by
    rw [halfDiff_flip, ← add_mul, cubeWeight_flip_add]
  have ha := sum_flip i (fun x => f x * (spin x i / 2) * deletedWeight z x i)
  have hb := sum_flip i (fun x => cubeWeight z x * halfDiff i f x)
  have h : (∑ x, cubeWeight z x * halfDiff i f x) +
      (∑ x, cubeWeight z (flip x i) * halfDiff i f (flip x i)) =
      (∑ x, f x * (spin x i / 2) * deletedWeight z x i) +
        (∑ x, f (flip x i) * (spin (flip x i) i / 2) * deletedWeight z (flip x i) i) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => (hB x).trans (hA x).symm)
  rw [ha, hb] at h
  linarith only [h]

lemma cubeExtension_line_deriv {n : ℕ} (f : Observables n) (a b : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => cubeExtension f (fun i => a i + s * b i))
      (∑ i, b i * ∑ x, cubeWeight (fun j => a j + t * b j) x * halfDiff i f x) t := by
  have hf (x : Spin n) (i : Fin n) :
      HasDerivAt (fun s : ℝ => (1 + spin x i * (a i + s * b i)) / 2)
        (spin x i * b i / 2) t := by
    simpa only [one_mul, id_eq] using (((((hasDerivAt_id t).mul_const (b i)).const_add (a i)).const_mul
      (spin x i)).const_add 1).div_const 2
  have hp (x : Spin n) :=
    (HasDerivAt.finsetProd (u := Finset.univ) (fun i _ => hf x i)).mul_const (f x)
  have h := HasDerivAt.sum (u := Finset.univ) (fun x _ => hp x)
  have hd : (∑ x, (∑ i, (∏ j ∈ Finset.univ.erase i,
        (1 + spin x j * (a j + t * b j)) / 2) • (spin x i * b i / 2)) * f x) =
      ∑ i, b i * ∑ x, cubeWeight (fun j => a j + t * b j) x * halfDiff i f x := by
    simp only [smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [cubeWeight_halfDiff, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    dsimp only [deletedWeight]
    ring
  rw [hd] at h
  have he : (∑ x, fun y : ℝ => (∏ i, (1 + spin x i * (a i + y * b i)) / 2) * f x) =
      (fun s : ℝ => cubeExtension f (fun i => a i + s * b i)) := by
    funext s
    simp only [Finset.sum_apply, cubeExtension, cubeWeight]
  simp only [Finset.prod_apply] at h
  rw [he] at h
  exact h

lemma weighted_mean_sq_le {α : Type*} [Fintype α] (p f : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) :
    (∑ x, p x * f x) ^ 2 ≤ ∑ x, p x * f x ^ 2 := by
  have h : 0 ≤ ∑ x, p x * (f x - ∑ y, p y * f y) ^ 2 := by
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (sq_nonneg _))
  simp_rw [sub_sq, mul_add, mul_sub] at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at h
  have h1 : (∑ x, p x * (2 * f x * ∑ y, p y * f y)) =
      2 * (∑ x, p x * f x) ^ 2 := by
    simp_rw [show ∀ x, p x * (2 * f x * ∑ y, p y * f y) =
      2 * (p x * f x) * (∑ y, p y * f y) by intro x; ring]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have h2 : (∑ x, p x * (∑ y, p y * f y) ^ 2) = (∑ y, p y * f y) ^ 2 := by
    rw [← Finset.sum_mul, hs, one_mul]
  rw [h1, h2] at h
  linarith only [h]

lemma cubeExtension_gradient_sq_le {n : ℕ} (f : Observables n) (z : Fin n → ℝ)
    (hz : ∀ i, -1 ≤ z i ∧ z i ≤ 1) (C : ℝ)
    (hf : ∀ x, ∑ i, (halfDiff i f x) ^ 2 ≤ C ^ 2) :
    (∑ i, (∑ x, cubeWeight z x * halfDiff i f x) ^ 2) ≤ C ^ 2 := by
  calc
    _ ≤ ∑ i, ∑ x, cubeWeight z x * (halfDiff i f x) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact weighted_mean_sq_le _ _ (cubeWeight_nonneg z hz) (cubeWeight_sum z)
    _ = ∑ x, cubeWeight z x * ∑ i, (halfDiff i f x) ^ 2 := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ x, cubeWeight z x * C ^ 2 := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (hf x) (cubeWeight_nonneg z hz x)
    _ = C ^ 2 := by rw [← Finset.sum_mul, cubeWeight_sum, one_mul]

lemma spin_segment_mem {n : ℕ} (x y : Spin n) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin n) : -1 ≤ spin x i + t * (spin y i - spin x i) ∧
      spin x i + t * (spin y i - spin x i) ≤ 1 := by
  rcases ht with ⟨hl, hu⟩
  cases hx : x i <;> cases hy : y i <;>
    simp only [spin, hx, hy, Bool.false_eq_true, ↓reduceIte] <;> constructor <;> nlinarith

lemma spin_vertex_distance_sq {n : ℕ} (x y : Spin n) :
    (∑ i, (spin y i - spin x i) ^ 2) ≤ 4 * n := by
  calc
    _ ≤ ∑ _i : Fin n, (4 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      cases hx : x i <;> cases hy : y i <;>
        norm_num [spin, hx, hy]
    _ = _ := by simp; ring

lemma cubeExtension_direction_bound {n : ℕ} (f : Observables n) (z b : Fin n → ℝ)
    (hz : ∀ i, -1 ≤ z i ∧ z i ≤ 1) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x, ∑ i, (halfDiff i f x) ^ 2 ≤ C ^ 2)
    (hb : ∑ i, (b i) ^ 2 ≤ 4 * n) :
    |∑ i, b i * ∑ x, cubeWeight z x * halfDiff i f x| ≤ 2 * Real.sqrt n * C := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hg := cubeExtension_gradient_sq_le f z hz C hf
  have hs : (∑ i, b i * ∑ x, cubeWeight z x * halfDiff i f x) ^ 2 ≤
      (2 * Real.sqrt n * C) ^ 2 := by
    calc
      _ ≤ (∑ i, (b i) ^ 2) * (∑ i, (∑ x, cubeWeight z x * halfDiff i f x) ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
      _ ≤ (4 * n) * C ^ 2 := mul_le_mul hb hg
        (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (by positivity)
      _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hn]; ring
  exact le_of_sq_le_sq (by simpa only [sq_abs] using hs) (by positivity)

theorem euclidean_oscillation {n : ℕ} (f : Observables n) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x, ∑ i, (halfDiff i f x) ^ 2 ≤ C ^ 2) (x y : Spin n) :
    |f x - f y| ≤ 2 * Real.sqrt n * C := by
  let F : ℝ → ℝ := fun t => cubeExtension f (fun i => spin x i + t * (spin y i - spin x i))
  have hd (t : ℝ) := cubeExtension_line_deriv f (spin x) (fun i => spin y i - spin x i) t
  have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ F t :=
    fun t _ => (hd t).differentiableAt
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖deriv F t‖ ≤ 2 * Real.sqrt n * C := by
    intro t ht
    rw [(hd t).deriv, Real.norm_eq_abs]
    exact cubeExtension_direction_bound f _ _ (spin_segment_mem x y t ht) C hC hf
      (spin_vertex_distance_sq x y)
  have hv := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (by simp : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
      (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  have hf0 : F 0 = f x := by simp [F, cubeExtension_vertex]
  have hf1 : F 1 = f y := by simp [F, cubeExtension_vertex]
  rw [hf0, hf1, sub_zero, norm_one, mul_one, Real.norm_eq_abs, abs_sub_comm] at hv
  exact hv

end SKGapCutoff

open scoped BigOperators

end

end OAI
