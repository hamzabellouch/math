import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Classes

namespace OAI

noncomputable section
open scoped ENNReal
namespace Invariant233.WeightedShift

abbrev Hilbert := lp (fun _ : ℤ => ℂ) 2
abbrev Weight := lp (fun _ : ℤ => ℂ) ∞

def reindex (e : Equiv.Perm ℤ) : Hilbert ≃ₗᵢ[ℂ] Hilbert where
  toFun ξ := ⟨fun k => ξ (e k), memℓp_gen <|
    (e.summable_iff).2 ((lp.memℓp ξ).summable (by norm_num))⟩
  invFun ξ := ⟨fun k => ξ (e.symm k), memℓp_gen <|
    (e.symm.summable_iff).2 ((lp.memℓp ξ).summable (by norm_num))⟩
  left_inv ξ := by ext k; simp
  right_inv ξ := by ext k; simp
  map_add' ξ η := by ext k; rfl
  map_smul' c ξ := by ext k; rfl
  norm_map' ξ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.tsum_eq (fun k => ‖ξ k‖ ^ (2 : ENNReal).toReal)

def shift (m : ℤ) : Hilbert ≃ₗᵢ[ℂ] Hilbert := reindex (Equiv.addRight (-m))

def diagonal (w : Weight) : Hilbert →L[ℂ] Hilbert :=
  lp.mapCLM 2 (fun k => w k • ContinuousLinearMap.id ℂ ℂ) (norm_nonneg w)
    (fun k => by
      let : T0Space ℂ := @MetricSpace.instT0Space ℂ Complex.instNormedAddCommGroup.toMetricSpace
      simpa [norm_smul] using lp.norm_apply_le_norm (by simp) w k)

def diagonalAlgHom : Weight →ₐ[ℂ] (Hilbert →L[ℂ] Hilbert) where
  toFun := diagonal
  map_one' := by
    ext ξ k
    change (1 : ℂ) * ξ k = ξ k
    exact one_mul _
  map_mul' w v := by
    ext ξ k
    change (w k * v k) * ξ k = w k * (v k * ξ k)
    exact mul_assoc _ _ _
  map_zero' := by
    ext ξ k
    change (0 : ℂ) * ξ k = 0
    exact zero_mul _
  map_add' w v := by
    ext ξ k
    change (w k + v k) * ξ k = w k * ξ k + v k * ξ k
    exact add_mul _ _ _
  commutes' c := by
    ext ξ k
    change c * ξ k = c * ξ k
    rfl

def translate (w : Weight) (m : ℤ) : Weight :=
  ⟨fun k => w (k + m), memℓp_infty <| by
    refine ⟨‖w‖, ?_⟩
    rintro r ⟨k, rfl⟩
    exact lp.norm_apply_le_norm (by simp) w (k + m)⟩

def operator (w : Weight) : Hilbert →L[ℂ] Hilbert :=
  (shift 1).toLinearIsometry.toContinuousLinearMap.comp (diagonal w)

def orbitProduct (w : Weight) (n : ℕ) : Weight :=
  ⟨fun k => ∏ j ∈ Finset.range n, w (k + j), memℓp_infty <| by
    refine ⟨‖w‖ ^ n, ?_⟩
    rintro r ⟨k, rfl⟩
    calc
      ‖∏ j ∈ Finset.range n, w (k + j)‖ ≤
          ∏ j ∈ Finset.range n, ‖w (k + j)‖ := le_of_eq (norm_prod _ _)
      _ ≤ ∏ _j ∈ Finset.range n, ‖w‖ := by
        apply Finset.prod_le_prod₀
        · intro j hj; exact norm_nonneg _
        · intro j hj; exact lp.norm_apply_le_norm (by simp) w _
      _ = ‖w‖ ^ n := by simp⟩

def tailWeight (m : ℤ) : Weight :=
  ⟨fun k => if m ≤ k then 1 else 0, memℓp_infty <| by
    refine ⟨1, ?_⟩
    rintro r ⟨k, rfl⟩
    by_cases h : m ≤ k <;> simp [h]⟩

def tailProjection (m : ℤ) : Hilbert →L[ℂ] Hilbert := diagonal (tailWeight m)

end Invariant233.WeightedShift

end

end OAI
