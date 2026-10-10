import OAI.Analysis.HyperbolicCones.FormBasic

namespace OAI

/-! A bilinear square dominated by the Choi--Lam form vanishes. -/

noncomputable section

open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

theorem form_linear_coordinates {W : Type u} [AddCommGroup W] [Module ℝ W]
    (f : (Fin 3 → ℝ) →ₗ[ℝ] W) (x : Fin 3 → ℝ) :
    f x = ∑ i, x i • f (Pi.single i 1) := by
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin 3 → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  simp

theorem form_bilinear_coordinates
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (z y : Fin 3 → ℝ) :
    l z y = ∑ i, ∑ j, (z i * y j) * l (Pi.single i 1) (Pi.single j 1) := by
  rw [form_linear_coordinates l z]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [form_linear_coordinates (l (Pi.single i 1)) y]
  simp [Finset.mul_sum, mul_assoc]

theorem dominated_form_vanishes_at_zero
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y)
    (z y : Fin 3 → ℝ) (hz : choiLam z y = 0) : l z y = 0 := by
  have hh := h z y
  rw [hz] at hh
  nlinarith [sq_nonneg (l z y)]

theorem dominated_form_cyclic_coefficient
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) (i : Fin 3) :
    l (Pi.single i 1) (Pi.single (i + 2) 1) = 0 :=
  dominated_form_vanishes_at_zero l h _ _ (choiLam_cyclic_zero i)

theorem dominated_form_sign_zero
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y)
    (σ : Fin 3 → ℝ) (hσ : ∀ i, σ i = 1 ∨ σ i = -1) : l σ σ = 0 :=
  dominated_form_vanishes_at_zero l h σ σ (choiLam_sign_zero σ hσ)

theorem dominated_form_symmetric_coefficients
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) :
    (l (Pi.single 0 1) (Pi.single 1 1) + l (Pi.single 1 1) (Pi.single 0 1) = 0) ∧
    (l (Pi.single 0 1) (Pi.single 2 1) + l (Pi.single 2 1) (Pi.single 0 1) = 0) ∧
    (l (Pi.single 1 1) (Pi.single 2 1) + l (Pi.single 2 1) (Pi.single 1 1) = 0) := by
  have h0 := dominated_form_vanishes_at_zero l h ![1, 1, 1] ![1, 1, 1]
    (by simp [choiLam_expand, Matrix.cons_val]; norm_num)
  have h1 := dominated_form_vanishes_at_zero l h ![1, 1, -1] ![1, 1, -1]
    (by simp [choiLam_expand, Matrix.cons_val]; norm_num)
  have h2 := dominated_form_vanishes_at_zero l h ![1, -1, 1] ![1, -1, 1]
    (by simp [choiLam_expand, Matrix.cons_val]; norm_num)
  have h3 := dominated_form_vanishes_at_zero l h ![-1, 1, 1] ![-1, 1, 1]
    (by simp [choiLam_expand, Matrix.cons_val]; norm_num)
  rw [form_bilinear_coordinates] at h0 h1 h2 h3
  simp [Fin.sum_univ_succ] at h0 h1 h2 h3
  constructor
  · linarith
  constructor <;> linarith

theorem dominated_form_off_diagonal
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) (i j : Fin 3) (hij : i ≠ j) :
    l (Pi.single i 1) (Pi.single j 1) = 0 := by
  obtain ⟨h01, h02, h12⟩ := dominated_form_symmetric_coefficients l h
  have h20 := dominated_form_cyclic_coefficient l h 0
  have h10 := dominated_form_cyclic_coefficient l h 1
  have h21 := dominated_form_cyclic_coefficient l h 2
  simp only [Fin.reduceAdd] at h20 h10 h21
  fin_cases i <;> fin_cases j <;> simp_all [Fin.reduceEq]

theorem form_curve_of_off_diagonal
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (hoff : ∀ i j : Fin 3, i ≠ j → l (Pi.single i 1) (Pi.single j 1) = 0)
    (i : Fin 3) (s : ℝ) :
    l ((Pi.single i 1 : Fin 3 → ℝ) + s • Pi.single (i + 2) 1)
      (Pi.single (i + 2) 1 + s • Pi.single i 1) =
      s * (l (Pi.single i 1) (Pi.single i 1) +
        l (Pi.single (i + 2) 1) (Pi.single (i + 2) 1)) := by
  have hi : i ≠ i + 2 := by fin_cases i <;> decide
  simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hoff i (i + 2) hi, hoff (i + 2) i hi.symm]
  ring

theorem dominated_form_diagonal_formula
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) (z y : Fin 3 → ℝ) :
    l z y = ∑ i, z i * y i * l (Pi.single i 1) (Pi.single i 1) := by
  rw [form_bilinear_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    simp [dominated_form_off_diagonal l h i j (Ne.symm hji)]
  · simp

theorem dominated_form_diagonal_pair_bound
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) (i : Fin 3) (s : ℝ) (hs : s ≠ 0) :
    (l (Pi.single i 1) (Pi.single i 1) +
      l (Pi.single (i + 2) 1) (Pi.single (i + 2) 1)) ^ 2 ≤ s ^ 2 := by
  have hh := h ((Pi.single i 1 : Fin 3 → ℝ) + s • Pi.single (i + 2) 1)
    (Pi.single (i + 2) 1 + s • Pi.single i 1)
  rw [choiLam_curve, form_curve_of_off_diagonal l (dominated_form_off_diagonal l h)] at hh
  apply le_of_mul_le_mul_left (a := s ^ 2) _ (sq_pos_of_ne_zero hs)
  nlinarith only [hh]

theorem dominated_form_diagonal_pair_zero
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) (i : Fin 3) :
    l (Pi.single i 1) (Pi.single i 1) +
      l (Pi.single (i + 2) 1) (Pi.single (i + 2) 1) = 0 := by
  let c := l (Pi.single i 1) (Pi.single i 1) +
    l (Pi.single (i + 2) 1) (Pi.single (i + 2) 1)
  change c = 0
  by_contra hc
  have hh := dominated_form_diagonal_pair_bound l h i (c / 2) (div_ne_zero hc (by norm_num))
  change c ^ 2 ≤ (c / 2) ^ 2 at hh
  nlinarith [sq_pos_of_ne_zero hc]

theorem dominated_form_diagonal_zero
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) (i : Fin 3) :
    l (Pi.single i 1) (Pi.single i 1) = 0 := by
  have h0 := dominated_form_diagonal_pair_zero l h 0
  have h1 := dominated_form_diagonal_pair_zero l h 1
  have h2 := dominated_form_diagonal_pair_zero l h 2
  simp only [Fin.reduceAdd] at h0 h1 h2
  fin_cases i <;> simp only [Fin.reduceFinMk] <;> linarith

theorem dominated_form_coefficient_zero
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) (i j : Fin 3) :
    l (Pi.single i 1) (Pi.single j 1) = 0 := by
  by_cases hij : i = j
  · subst j
    exact dominated_form_diagonal_zero l h i
  · exact dominated_form_off_diagonal l h i j hij

theorem choiLam_no_dominated_square
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) : l = 0 := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro y
  change l z y = 0
  rw [form_bilinear_coordinates]
  simp [dominated_form_coefficient_zero l h]

end Paper256

end

end OAI
