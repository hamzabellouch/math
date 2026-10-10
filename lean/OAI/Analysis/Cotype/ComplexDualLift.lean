import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Complex.Basic

namespace OAI

noncomputable section
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

abbrev ComplexDualSpace (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y] :=
  (Y →L[ℝ] ℝ) →L[ℝ] ℂ

instance complexDualSpaceNormedAddCommGroup : NormedAddCommGroup (ComplexDualSpace Y) :=
  ContinuousLinearMap.toNormedAddCommGroup

instance complexDualSpaceNormedSpace : NormedSpace ℂ (ComplexDualSpace Y) :=
  ContinuousLinearMap.toNormedSpace

def realDualAction (T : Y →L[ℝ] Y) : (Y →L[ℝ] ℝ) →L[ℝ] (Y →L[ℝ] ℝ) :=
  ({ toFun := fun φ => φ.comp T
     map_add' := by intros; ext; simp
     map_smul' := by intros; ext; simp } :
    (Y →L[ℝ] ℝ) →ₗ[ℝ] (Y →L[ℝ] ℝ)).mkContinuous ‖T‖
      (fun φ => (φ.opNorm_comp_le T).trans_eq (mul_comm _ _))

@[simp] theorem realDualAction_apply (T : Y →L[ℝ] Y) (φ : Y →L[ℝ] ℝ) :
    realDualAction T φ = φ.comp T := rfl

theorem realDualAction_norm_le (T : Y →L[ℝ] Y) : ‖realDualAction T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro φ
  exact (φ.opNorm_comp_le T).trans_eq (mul_comm _ _)

def complexDualLift (T : Y →L[ℝ] Y) : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y :=
  ({ toFun := fun f => f.comp (realDualAction T)
     map_add' := by intros; ext; simp
     map_smul' := by intros; ext; simp } :
    ComplexDualSpace Y →ₗ[ℂ] ComplexDualSpace Y).mkContinuous ‖T‖ (fun f =>
      (f.opNorm_comp_le _).trans ((mul_le_mul_of_nonneg_left
        (realDualAction_norm_le T) (norm_nonneg f)).trans_eq (mul_comm _ _)))

@[simp] theorem complexDualLift_apply (T : Y →L[ℝ] Y)
    (f : ComplexDualSpace Y) (φ : Y →L[ℝ] ℝ) :
    complexDualLift T f φ = f (φ.comp T) := rfl

theorem complexDualLift_norm_le (T : Y →L[ℝ] Y) : ‖complexDualLift T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  exact (f.opNorm_comp_le _).trans ((mul_le_mul_of_nonneg_left
    (realDualAction_norm_le T) (norm_nonneg f)).trans_eq (mul_comm _ _))

def complexDualEmbed (y : Y) : ComplexDualSpace Y :=
  Complex.ofRealCLM.comp (NormedSpace.inclusionInDoubleDual ℝ Y y)

@[simp] theorem complexDualEmbed_apply (y : Y) (φ : Y →L[ℝ] ℝ) :
    complexDualEmbed y φ = (φ y : ℂ) := rfl

@[simp] theorem complexDualEmbed_norm (y : Y) : ‖complexDualEmbed y‖ = ‖y‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y)
    intro φ
    simpa only [complexDualEmbed_apply, Complex.norm_real, Real.norm_eq_abs,
      mul_comm] using φ.le_opNorm y
  · apply NormedSpace.norm_le_dual_bound ℝ y (norm_nonneg (complexDualEmbed y))
    intro φ
    simpa only [complexDualEmbed_apply, Complex.norm_real, Real.norm_eq_abs] using
      (complexDualEmbed y).le_opNorm φ

@[simp] theorem complexDualLift_embed (T : Y →L[ℝ] Y) (y : Y) :
    complexDualLift T (complexDualEmbed y) = complexDualEmbed (T y) := by
  ext φ
  rfl

theorem complexDualLift_norm (T : Y →L[ℝ] Y) : ‖complexDualLift T‖ = ‖T‖ := by
  apply le_antisymm (complexDualLift_norm_le T)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro y
  simpa only [complexDualLift_embed, complexDualEmbed_norm] using
    (complexDualLift T).le_opNorm (complexDualEmbed y)

@[simp] theorem complexDualLift_one : complexDualLift (1 : Y →L[ℝ] Y) = 1 := by
  ext f φ
  change f (φ.comp (1 : Y →L[ℝ] Y)) = f φ
  congr 1

@[simp] theorem complexDualLift_mul (S T : Y →L[ℝ] Y) :
    complexDualLift (S*T) = complexDualLift S * complexDualLift T := by
  ext f φ
  rfl

@[simp] theorem complexDualLift_add (S T : Y →L[ℝ] Y) :
    complexDualLift (S+T) = complexDualLift S + complexDualLift T := by
  ext f φ
  change f (φ.comp (S+T)) = f (φ.comp S) + f (φ.comp T)
  rw [ContinuousLinearMap.comp_add, map_add]

@[simp] theorem complexDualLift_sub (S T : Y →L[ℝ] Y) :
    complexDualLift (S-T) = complexDualLift S - complexDualLift T := by
  ext f φ
  change f (φ.comp (S-T)) = f (φ.comp S) - f (φ.comp T)
  rw [ContinuousLinearMap.comp_sub, map_sub]

@[simp] theorem complexDualLift_smul (r : ℝ) (T : Y →L[ℝ] Y) :
    complexDualLift (r • T) = r • complexDualLift T := by
  ext f φ
  change f (φ.comp (r • T)) = r • f (φ.comp T)
  rw [ContinuousLinearMap.comp_smul, map_smul]

@[simp] theorem complexDualLift_pow (T : Y →L[ℝ] Y) (n : ℕ) :
    complexDualLift (T^n) = (complexDualLift T)^n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

theorem complexDualLift_power_gap (T : Y →L[ℝ] Y) {N : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ y, ‖((1-T)^N) y‖ ≤ C*‖y‖) :
    ∀ f : ComplexDualSpace Y, ‖((1-complexDualLift T)^N) f‖ ≤ C*‖f‖ := by
  have hnorm : ‖(1-T)^N‖ ≤ C := ContinuousLinearMap.opNorm_le_bound _ hC h
  have hlift : ‖(1-complexDualLift T)^N‖ ≤ C := by
    simpa only [← complexDualLift_one, ← complexDualLift_sub, ← complexDualLift_pow,
      complexDualLift_norm] using hnorm
  exact ContinuousLinearMap.le_of_opNorm_le _ hlift

end Cotype

end

end OAI
