import OAI.Analysis.Unitarizability.MaskAlgebra

namespace OAI

/-! Individual block row and column bounds from the endpoint assignment. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq G := Classical.decEq G
local instance : DecidableEq ℂ := Classical.decEq ℂ

theorem support_bound (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) {p : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v p b) (J : Finset I) (hJ : J.card ≤ p)
    (hs : ∀ x i, c x i ≠ 0 → i ∈ J) : ‖operator v s c hc‖ ≤ b^2 := by
  apply masked_bound_of_frame _ _ _ _ hb hv
  · intro x
    exact (Finset.card_le_card (fun i hi => hs x i (Finset.mem_filter.mp hi).2)).trans hJ
  · intro y
    exact (Finset.card_le_card (fun i hi => hs _ i (Finset.mem_filter.mp hi).2)).trans hJ

def rowMask (a : G → I → Bool) (x₀ x : G) (i : I) : ℂ :=
  if x = x₀ then boolComplex (a x i) else 0

def columnMask (a : G → I → Bool) (s : I → G) (y₀ x : G) (i : I) : ℂ :=
  if x * s i = y₀ then 1 - boolComplex (a x i) else 0

omit [Group G] [Fintype I] in
theorem rowMask_norm (a : G → I → Bool) (x₀ x : G) (i : I) : ‖rowMask a x₀ x i‖ ≤ 1 := by
  unfold rowMask
  split_ifs
  · exact bool_mask_norm a x i
  · simp

omit [Group G] [Fintype I] in
theorem complement_norm (a : G → I → Bool) (x : G) (i : I) : ‖1 - boolComplex (a x i)‖ ≤ 1 := by
  cases a x i <;> simp [boolComplex]

omit [Fintype I] in
theorem columnMask_norm (a : G → I → Bool) (s : I → G) (y₀ x : G) (i : I) :
    ‖columnMask a s y₀ x i‖ ≤ 1 := by
  unfold columnMask
  split_ifs
  · exact complement_norm a x i
  · simp

omit [Group G] in
theorem rowMask_support (a : G → I → Bool) (x₀ x : G) (i : I) (h : rowMask a x₀ x i ≠ 0) :
    i ∈ rowOnes a x₀ := by
  unfold rowMask at h
  split_ifs at h with he
  · subst x
    cases ha : a x₀ i <;> simp_all [boolComplex, rowOnes]
  · exact (h rfl).elim

theorem columnMask_support (a : G → I → Bool) (s : I → G) (y₀ x : G) (i : I)
    (h : columnMask a s y₀ x i ≠ 0) : i ∈ columnZeros a s y₀ := by
  unfold columnMask at h
  split_ifs at h with he
  · have hx : y₀ * (s i)⁻¹ = x := by rw [← he, mul_inv_cancel_right]
    cases ha : a x i <;> simp_all [boolComplex, columnZeros]
  · exact (h rfl).elim

theorem row_localization (v : I → Fibre K) (s : I → G) (a : G → I → Bool) (x₀ : G) :
    KernelObstruction.row (oriented v s a) x₀ =
      KernelObstruction.row (operator v s (rowMask a x₀) (rowMask_norm a x₀)) x₀ := by
  ext ξ z
  change (oriented v s a ξ x₀) z = (operator v s (rowMask a x₀) (rowMask_norm a x₀) ξ x₀) z
  simp [oriented, operator_apply, rowMask]

theorem column_localization (v : I → Fibre K) (s : I → G) (a : G → I → Bool) (y₀ : G) :
    KernelObstruction.col (constant v s - oriented v s a) y₀ =
      KernelObstruction.col (operator v s (columnMask a s y₀) (columnMask_norm a s y₀)) y₀ := by
  have hsub : constant v s - oriented v s a =
      operator v s (fun x i => 1 - boolComplex (a x i)) (complement_norm a) :=
    operator_sub _ _ _ _ _ _ _
  rw [hsub]
  apply ContinuousLinearMap.ext
  intro z
  apply lp.ext
  funext x
  change operator v s (fun x i => 1 - boolComplex (a x i)) (complement_norm a) (lp.single 2 y₀ z) x =
    operator v s (columnMask a s y₀) (columnMask_norm a s y₀) (lp.single 2 y₀ z) x
  simp only [operator_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : x * s i = y₀
  · simp [columnMask, h]
  · rw [lp.single_apply_ne _ _ _ h]
    simp [columnMask, h]

theorem local_row_bound (v : I → Fibre K) (s : I → G) (a : G → I → Bool)
    {r : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v (min (2*r) (Fintype.card I)) b)
    (hr : ∀ x, (rowOnes a x).card ≤ r) (x₀ : G) :
    ‖KernelObstruction.row (oriented v s a) x₀‖ ≤ b^2 := by
  have hJ : (rowOnes a x₀).card ≤ min (2*r) (Fintype.card I) :=
    le_min ((hr x₀).trans (by omega)) (Finset.card_le_univ _)
  have h := support_bound v s (rowMask a x₀) (rowMask_norm a x₀) hb hv (rowOnes a x₀) hJ
    (rowMask_support a x₀)
  rw [row_localization]
  exact (KernelObstruction.row_norm_le _ _).trans h

theorem local_column_bound (v : I → Fibre K) (s : I → G) (a : G → I → Bool)
    {r : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v (min (2*r) (Fintype.card I)) b)
    (hc : ∀ y, (columnZeros a s y).card ≤ r) (y₀ : G) :
    ‖KernelObstruction.col (constant v s - oriented v s a) y₀‖ ≤ b^2 := by
  have hJ : (columnZeros a s y₀).card ≤ min (2*r) (Fintype.card I) :=
    le_min ((hc y₀).trans (by omega)) (Finset.card_le_univ _)
  have h := support_bound v s (columnMask a s y₀) (columnMask_norm a s y₀) hb hv (columnZeros a s y₀) hJ
    (columnMask_support a s y₀)
  rw [column_localization]
  exact (KernelObstruction.col_norm_le _ _).trans h

end Masked
end Dixmier

end

end OAI
