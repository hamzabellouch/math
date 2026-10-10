import OAI.NumberTheory.Ostmann.Construction.FinitePriorComparison

namespace OAI

/-! # Exact pushforward to log-cell and residue coordinates

The finite partition of each actual prime sample induces independent cell
priors. This is an equality, before any progression approximation is used.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def cellPrior {A B : Type*} [Fintype A]
    (μ : A → ℝ) (cell : A → B) (b : B) : ℝ :=
  ∑ a, if cell a = b then μ a else 0

theorem cellPrior_nonneg {A B : Type*} [Fintype A]
    (μ : A → ℝ) (cell : A → B) (hμ : ∀ a, 0 ≤ μ a) (b : B) :
    0 ≤ cellPrior μ cell b := by
  apply Finset.sum_nonneg
  intro a _
  split
  · exact hμ a
  · exact le_rfl

theorem cellPrior_mass {A B : Type*} [Fintype A] [Fintype B]
    (μ : A → ℝ) (cell : A → B) : (∑ b, cellPrior μ cell b) = ∑ a, μ a := by
  unfold cellPrior
  rw [Finset.sum_comm]
  simp

private theorem product_cell_indicator {A B : Type*} {n : ℕ}
    (μ : Fin n → A → ℝ) (cell : Fin n → A → B) (x : Fin n → A) (y : Fin n → B) :
    (∏ i, if cell i (x i) = y i then μ i (x i) else 0) =
      if (fun i => cell i (x i)) = y then productPrior μ x else 0 := by
  by_cases h : (fun i => cell i (x i)) = y
  · have hi : ∀ i, cell i (x i) = y i := fun i => congrFun h i
    simp [hi, productPrior]
  · have hi : ∃ i, cell i (x i) ≠ y i := by
      by_contra hn
      apply h
      funext i
      exact not_not.mp (not_exists.mp hn i)
    obtain ⟨i, hi⟩ := hi
    rw [ite_eq_right_iff.mpr (fun hh => (h hh).elim)]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right_iff.mpr (fun hh => (hi hh).elim))

theorem product_cellPrior {A B : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (cell : Fin n → A → B) (y : Fin n → B) :
    productPrior (fun i => cellPrior (μ i) (cell i)) y =
      ∑ x : Fin n → A, if (fun i => cell i (x i)) = y then productPrior μ x else 0 := by
  unfold productPrior cellPrior
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact product_cell_indicator μ cell x y

/-- Joint sampling and then recording cells is exactly sampling the cell
priors. The statement keeps an arbitrary complex signed integrand. -/
theorem sum_productPrior_cells {A B : Type*} [Fintype A] [Fintype B] {n : ℕ}
    (μ : Fin n → A → ℝ) (cell : Fin n → A → B) (F : (Fin n → B) → ℂ) :
    (∑ x, (productPrior μ x : ℂ) * F (fun i => cell i (x i))) =
      ∑ y, (productPrior (fun i => cellPrior (μ i) (cell i)) y : ℂ) * F y := by
  simp_rw [product_cellPrior, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The per-class absolute error in the progression formula gives the
one-coordinate total-variation estimate after summing the partition. -/
theorem cellPrior_l1_le {A B : Type*} [Fintype A] [Fintype B]
    (μ : A → ℝ) (cell : A → B) (ν : B → ℝ) (δ : ℝ)
    (h : ∀ b, |cellPrior μ cell b - ν b| ≤ δ) :
    (∑ b, |cellPrior μ cell b - ν b|) ≤ Fintype.card B * δ := by
  calc
    _ ≤ ∑ _b : B, δ := Finset.sum_le_sum fun b _ => h b
    _ = _ := by simp

/-- The mass bound on the ideal prior follows from the actual mass and
the cell errors, so it need not be an independent analytic hypothesis. -/
theorem cellPrior_mass_comparison {A B : Type*} [Fintype A] [Fintype B]
    (μ : A → ℝ) (cell : A → B) (ν : B → ℝ) (δ : ℝ)
    (h : ∀ b, |cellPrior μ cell b - ν b| ≤ δ) :
    (∑ b, ν b) ≤ (∑ a, μ a) + Fintype.card B * δ := by
  calc
    _ ≤ ∑ b, (cellPrior μ cell b + δ) := Finset.sum_le_sum fun b _ => by
      have hb := (abs_le.mp (h b)).1
      linarith
    _ = _ := by rw [Finset.sum_add_distrib, cellPrior_mass]; simp

/-- Joint finite-cell idealization, including the error from freezing the
smooth amplitude. The residue correction is part of `ν` throughout. -/
theorem finite_cell_idealization {A C : Type*} [Fintype A] [Fintype C] {n : ℕ}
    (μ : Fin n → A → ℝ) (cell : Fin n → A → C) (ν : Fin n → C → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a) (hν : ∀ i c, 0 ≤ ν i c)
    (hmassμ : ∀ i, ∑ a, μ i a ≤ 2) (hmassν : ∀ i, ∑ c, ν i c ≤ 2)
    (δ B η : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (hdist : ∀ i c, |cellPrior (μ i) (cell i) c - ν i c| ≤ δ)
    (H : (Fin n → A) → ℂ) (F : (Fin n → C) → ℂ)
    (hF : ∀ y, ‖F y‖ ≤ B) (hfreeze : ∀ x, ‖H x - F (fun i => cell i (x i))‖ ≤ η) :
    ‖(∑ x, (productPrior μ x : ℂ) * H x) -
      (∑ y, (productPrior ν y : ℂ) * F y)‖ ≤
        η * 2 ^ n + B * n * (Fintype.card C * δ) * 2 ^ n := by
  have hvar := weighted_productPrior_variation μ hμ hmassμ H
    (fun x => F (fun i => cell i (x i))) η hη hfreeze
  have hcomp := weighted_productPrior_comparison
    (fun i => cellPrior (μ i) (cell i)) ν
    (fun i => cellPrior_nonneg (μ i) (cell i) (hμ i)) hν
    (fun i => by rw [cellPrior_mass]; exact hmassμ i) hmassν
    (Fintype.card C * δ) B (mul_nonneg (Nat.cast_nonneg _) hδ) hB
    (fun i => cellPrior_l1_le (μ i) (cell i) (ν i) δ (hdist i)) F hF
  rw [sum_productPrior_cells μ cell F] at hvar
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hvar hcomp)

/-- Joint idealization for probability samples. The ideal coordinate mass
is at most two as a consequence of the per-cell approximation. -/
theorem finite_cell_idealization_of_probability {A C : Type*}
    [Fintype A] [Fintype C] {n : ℕ}
    (μ : Fin n → A → ℝ) (cell : Fin n → A → C) (ν : Fin n → C → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a) (hν : ∀ i c, 0 ≤ ν i c)
    (hmassμ : ∀ i, ∑ a, μ i a ≤ 1)
    (δ B η : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (hsmall : Fintype.card C * δ ≤ 1)
    (hdist : ∀ i c, |cellPrior (μ i) (cell i) c - ν i c| ≤ δ)
    (H : (Fin n → A) → ℂ) (F : (Fin n → C) → ℂ)
    (hF : ∀ y, ‖F y‖ ≤ B) (hfreeze : ∀ x, ‖H x - F (fun i => cell i (x i))‖ ≤ η) :
    ‖(∑ x, (productPrior μ x : ℂ) * H x) -
      (∑ y, (productPrior ν y : ℂ) * F y)‖ ≤
        η * 2 ^ n + B * n * (Fintype.card C * δ) * 2 ^ n := by
  apply finite_cell_idealization μ cell ν hμ hν
    (fun i => (hmassμ i).trans (by norm_num)) _ δ B η hδ hB hη hdist H F hF hfreeze
  intro i
  exact (cellPrior_mass_comparison (μ i) (cell i) (ν i) δ (hdist i)).trans (by linarith [hmassμ i])

end Ostmann

end OAI
