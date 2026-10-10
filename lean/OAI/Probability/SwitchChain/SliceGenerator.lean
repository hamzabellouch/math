import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceGenerator

theorem sum_swap_coordinate
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (k : α) :
    (∑ i, ∑ j, (x k - x (Equiv.swap i j k))) =
      2 * ((Fintype.card α : ℝ) * x k - ∑ i, x i) := by
  have inner_sum (i : α) :
      (∑ j, (x k - x (Equiv.swap i j k))) =
        (if i = k then (Fintype.card α : ℝ) * x k - ∑ j, x j else 0) +
          (x k - x i) := by
    by_cases hi : i = k
    · subst i
      simp [Finset.sum_sub_distrib, mul_comm]
    · have hterm (j : α) :
          x k - x (Equiv.swap i j k) = if j = k then x k - x i else 0 := by
        by_cases hj : j = k
        · subst j
          simp
        · simp [Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj), hj]
      simp_rw [hterm]
      simp [hi]
  simp_rw [inner_sum]
  simp only [Finset.sum_add_distrib]
  simp [Finset.sum_sub_distrib, mul_comm]
  ring

theorem sum_swap_coordinate_cross
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (k l : α) (hkl : k ≠ l) :
    (∑ i, ∑ j,
      (x k - x (Equiv.swap i j k)) * (x l - x (Equiv.swap i j l))) =
      -2 * (x k - x l) ^ 2 := by
  have hterm (i j : α) :
      (x k - x (Equiv.swap i j k)) * (x l - x (Equiv.swap i j l)) =
        (if i = k ∧ j = l then -(x k - x l) ^ 2 else 0) +
        (if i = l ∧ j = k then -(x k - x l) ^ 2 else 0) := by
    by_cases hik : i = k <;> by_cases hil : i = l <;>
      by_cases hjk : j = k <;> by_cases hjl : j = l <;>
      simp_all [Equiv.swap_apply_def, eq_comm] <;> ring
  simp_rw [hterm, Finset.sum_add_distrib]
  simp_rw [ite_and]
  simp
  ring

theorem sum_swap_quadratic
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (k l : α) (hkl : k ≠ l) :
    (∑ i, ∑ j,
      (x k * x l - x (Equiv.swap i j k) * x (Equiv.swap i j l))) =
      4 * ((Fintype.card α : ℝ) - 1) * x k * x l +
      2 * (x k ^ 2 + x l ^ 2) - 2 * (∑ i, x i) * (x k + x l) := by
  calc
    _ = ∑ i, ∑ j,
        (x l * (x k - x (Equiv.swap i j k)) +
         x k * (x l - x (Equiv.swap i j l)) -
         (x k - x (Equiv.swap i j k)) * (x l - x (Equiv.swap i j l))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = x l * (∑ i, ∑ j, (x k - x (Equiv.swap i j k))) +
        x k * (∑ i, ∑ j, (x l - x (Equiv.swap i j l))) -
        (∑ i, ∑ j,
          (x k - x (Equiv.swap i j k)) * (x l - x (Equiv.swap i j l))) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      rw [sum_swap_coordinate, sum_swap_coordinate,
        sum_swap_coordinate_cross x k l hkl]
      ring

def generator {α : Type*} [Fintype α] [DecidableEq α]
    (f : (α → ℝ) → ℝ) (x : α → ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, ∑ j, (f x - f (x ∘ Equiv.swap i j))

theorem generator_coordinate
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (q : ℝ) (hsum : ∑ i, x i = q) (k : α) :
    generator (fun y => y k) x = ((Fintype.card α : ℝ) * x k - q) / 2 := by
  unfold generator
  simp only [Function.comp_apply]
  rw [sum_swap_coordinate, hsum]
  ring

theorem generator_quadratic
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (q : ℝ) (hsum : ∑ i, x i = q)
    (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (k l : α) (hkl : k ≠ l) :
    generator (fun y => y k * y l) x =
      ((Fintype.card α : ℝ) - 1) * x k * x l - (q - 1) / 2 * (x k + x l) := by
  have hsq (i : α) : x i ^ 2 = x i := by
    rcases hbinary i with h | h <;> simp [h]
  unfold generator
  simp only [Function.comp_apply]
  rw [sum_swap_quadratic x k l hkl, hsum, hsq k, hsq l]
  ring

def generatorLinearMap {α : Type*} [Fintype α] [DecidableEq α] :
    ((α → ℝ) → ℝ) →ₗ[ℝ] ((α → ℝ) → ℝ) where
  toFun := generator
  map_add' f g := by
    ext x
    simp only [generator, Pi.add_apply]
    simp_rw [show ∀ a b c d : ℝ, a + b - (c + d) = (a-c) + (b-d) by intros; ring]
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    ext x
    simp only [generator, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [← mul_sub, ← Finset.mul_sum]
    ring

theorem generator_centered_linear
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (u : α → ℝ) (hu : ∑ i, u i = 0) :
    generator (fun y => ∑ i, u i * y i) x =
      (Fintype.card α : ℝ) / 2 * (∑ i, u i * x i) := by
  have heq : (fun y : α → ℝ => ∑ i, u i * y i) =
      ∑ i, u i • (fun y : α → ℝ => y i) := by
    ext y
    simp
  change generatorLinearMap (fun y => ∑ i, u i * y i) x = _
  rw [heq, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i, u i * generator (fun y => y i) x) = _
  simp_rw [generator_coordinate x (∑ j, x j) rfl]
  simp_rw [← mul_div_assoc, ← Finset.sum_div, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hu, zero_mul, sub_zero]
  rw [show (∑ i, u i * ((Fintype.card α : ℝ) * x i)) =
      (Fintype.card α : ℝ) * ∑ i, u i * x i by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring]
  ring

theorem sum_coeff_linear_eq_zero
    {α : Type*} [Fintype α]
    (c : α → α → ℝ) (x : α → ℝ)
    (hrow : ∀ i, ∑ j, c i j = 0) (hcol : ∀ j, ∑ i, c i j = 0) :
    (∑ i, ∑ j, c i j * (x i + x j)) = 0 := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hleft : (∑ i, ∑ j, c i j * x i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.sum_mul, hrow, zero_mul]
  have hright : (∑ i, ∑ j, c i j * x j) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    rw [← Finset.sum_mul, hcol, zero_mul]
  rw [hleft, hright, add_zero]

theorem generator_row_zero_quadratic
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (q : ℝ) (hsum : ∑ i, x i = q)
    (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (c : α → α → ℝ) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, ∑ j, c i j = 0) (hcol : ∀ j, ∑ i, c i j = 0) :
    generator (fun y => ∑ i, ∑ j, c i j * (y i * y j)) x =
      ((Fintype.card α : ℝ) - 1) * (∑ i, ∑ j, c i j * (x i * x j)) := by
  have heq : (fun y : α → ℝ => ∑ i, ∑ j, c i j * (y i * y j)) =
      ∑ i, ∑ j, c i j • (fun y : α → ℝ => y i * y j) := by
    ext y
    simp
  change generatorLinearMap (fun y => ∑ i, ∑ j, c i j * (y i * y j)) x = _
  rw [heq, map_sum]
  simp_rw [map_sum, map_smul]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i, ∑ j, c i j * generator (fun y => y i * y j) x) = _
  have hterm (i j : α) : c i j * generator (fun y => y i * y j) x =
      ((Fintype.card α : ℝ) - 1) * (c i j * (x i * x j)) -
        (q - 1) / 2 * (c i j * (x i + x j)) := by
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · rw [generator_quadratic x q hsum hbinary i j hij]
      ring
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_coeff_linear_eq_zero c x hrow hcol]
  ring

theorem generator_symmetric_row_zero_quadratic
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (q : ℝ) (hsum : ∑ i, x i = q)
    (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (c : α → α → ℝ) (hdiag : ∀ i, c i i = 0)
    (hsymm : ∀ i j, c i j = c j i) (hrow : ∀ i, ∑ j, c i j = 0) :
    generator (fun y => ∑ i, ∑ j, c i j * (y i * y j)) x =
      ((Fintype.card α : ℝ) - 1) * (∑ i, ∑ j, c i j * (x i * x j)) := by
  apply generator_row_zero_quadratic x q hsum hbinary c hdiag hrow
  intro j
  simpa only [hsymm] using hrow j

end Problem315.SliceGenerator

end

end OAI
