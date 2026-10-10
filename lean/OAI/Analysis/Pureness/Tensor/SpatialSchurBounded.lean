import OAI.Analysis.Pureness.Tensor.SpatialSchurNorm
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI
noncomputable section
namespace CuntzPureness
local instance spatialSchurBoundedDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
open CuntzComparison
open scoped InnerProductSpace
variable {H V G : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem spatialSchur_norm_le_bound (C : ℝ) (hC : 0 < C) (v w : G → V)
    (hv : ∀ g, ‖v g‖ ≤ C) (hw : ∀ g, ‖w g‖ ≤ C)
    (S T : SpatialHilbert H (GroupL2 G) →L[ℂ] SpatialHilbert H (GroupL2 G))
    (he : ∀ g h,
      (spatialRightVector (H := H) (lp.single 2 g (1 : ℂ))).adjoint.comp
        (S.comp (spatialRightVector (lp.single 2 h (1 : ℂ)))) =
      ⟪v g, w h⟫_ℂ •
        (spatialRightVector (H := H) (lp.single 2 g (1 : ℂ))).adjoint.comp
          (T.comp (spatialRightVector (lp.single 2 h (1 : ℂ))))) :
    ‖S‖ ≤ C ^ 2 * ‖T‖ := by
  let v' : G → V := fun g => ((C⁻¹ : ℝ) : ℂ) • v g
  let w' : G → V := fun g => ((C⁻¹ : ℝ) : ℂ) • w g
  have hv' (g : G) : ‖v' g‖ ≤ 1 := by
    dsimp [v']; simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hC)]
    exact (mul_le_mul_of_nonneg_left (hv g) (inv_nonneg.mpr hC.le)).trans_eq (inv_mul_cancel₀ hC.ne')
  have hw' (g : G) : ‖w' g‖ ≤ 1 := by
    dsimp [w']; simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hC)]
    exact (mul_le_mul_of_nonneg_left (hw g) (inv_nonneg.mpr hC.le)).trans_eq (inv_mul_cancel₀ hC.ne')
  have hb := spatialSchur_norm_le v' w' hv' hw' S (((C ^ 2 : ℝ) : ℂ) • T) ?_
  · apply hb.trans
    calc
      _ ≤ ‖((C ^ 2 : ℝ) : ℂ)‖ * ‖T‖ := ContinuousLinearMap.opNorm_smul_le ((C ^ 2 : ℝ) : ℂ) T
      _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg C)]
  · intro g h
    rw [he]
    simp only [v', w', inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
    congr 1
    have hc : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
    push_cast
    field_simp

theorem spatialSchur_norm_le_fintype_sum {I : Type*} [Fintype I]
    (c : I → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1) (v w : I → G → V)
    (hv : ∀ i g, ‖v i g‖ ≤ 1) (hw : ∀ i g, ‖w i g‖ ≤ 1)
    (S T : SpatialHilbert H (GroupL2 G) →L[ℂ] SpatialHilbert H (GroupL2 G))
    (he : ∀ g h,
      (spatialRightVector (H := H) (lp.single 2 g (1 : ℂ))).adjoint.comp
        (S.comp (spatialRightVector (lp.single 2 h (1 : ℂ)))) =
      (∑ i, c i * ⟪v i g, w i h⟫_ℂ) •
        (spatialRightVector (H := H) (lp.single 2 g (1 : ℂ))).adjoint.comp
          (T.comp (spatialRightVector (lp.single 2 h (1 : ℂ))))) :
    ‖S‖ ≤ ((Fintype.card I : ℝ) + 1) ^ 2 * ‖T‖ := by
  let v' : G → PiLp 2 (fun _ : I => V) := fun g => WithLp.toLp 2 (fun i => v i g)
  let w' : G → PiLp 2 (fun _ : I => V) := fun g => WithLp.toLp 2 (fun i => c i • w i g)
  have bound (f : I → V) (hf : ∀ i, ‖f i‖ ≤ 1) :
      ‖(WithLp.toLp 2 f : PiLp 2 (fun _ : I => V))‖ ≤ (Fintype.card I : ℝ) + 1 := by
    have hsq : ‖(WithLp.toLp 2 f : PiLp 2 (fun _ : I => V))‖ ^ 2 ≤ (Fintype.card I : ℝ) := by
      rw [PiLp.norm_sq_eq_of_L2]
      calc
        _ ≤ ∑ i : I, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
          change ‖f i‖ ^ 2 ≤ 1
          nlinarith [hf i, norm_nonneg (f i)])
        _ = _ := by simp
    have hn : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
    nlinarith [norm_nonneg (WithLp.toLp 2 f : PiLp 2 (fun _ : I => V))]
  apply spatialSchur_norm_le_bound ((Fintype.card I : ℝ) + 1) (by positivity) v' w'
    (fun g => bound _ (fun i => hv i g))
    (fun g => bound _ (fun i => by
      rw [norm_smul]
      exact (mul_le_mul (hc i) (hw i g) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))) S T
  intro g h
  rw [he]
  congr 1
  simp [v', w', PiLp.inner_apply, inner_smul_right]
end CuntzPureness

end

end OAI
