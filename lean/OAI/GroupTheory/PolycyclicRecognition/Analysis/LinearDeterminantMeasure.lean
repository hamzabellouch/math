import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Determinant

namespace OAI

/-! # A volume-preserving linear equivalence has determinant of absolute value one -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

theorem abs_det_eq_one_of_measurePreserving_linearMap {n : ℕ}
    (F : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (hd : LinearMap.det F ≠ 0)
    (hF : MeasurePreserving F volume volume) :
    |LinearMap.det F| = 1 := by
  have he : ENNReal.ofReal |(LinearMap.det F)⁻¹| •
      (volume : Measure (Fin n → ℝ)) = volume := by
    rw [← Real.map_linearMap_volume_pi_eq_smul_volume_pi hd]
    exact hF.map_eq
  have hv : (volume : Measure (Fin n → ℝ)) (Icc 0 1) = 1 := by
    simp [Real.volume_Icc_pi]
  have hh := congrArg (fun μ : Measure (Fin n → ℝ) => μ (Icc 0 1)) he
  rw [Measure.smul_apply, hv, smul_eq_mul, mul_one] at hh
  have hr := congrArg ENNReal.toReal hh
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_one, abs_inv] at hr
  exact inv_injective (by simpa only [inv_one] using hr)

theorem abs_det_eq_one_of_measurePreserving {n : ℕ}
    (F : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hF : MeasurePreserving F volume volume) :
    |LinearMap.det F.toLinearMap| = 1 :=
  abs_det_eq_one_of_measurePreserving_linearMap F.toLinearMap F.isUnit_det'.ne_zero hF

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem det_eq_restrict_of_quotient_eq_id (U : Submodule ℝ V)
    (F : V →ₗ[ℝ] V) (hU : U ≤ U.comap F)
    (hquot : U.mapQ U F hU = LinearMap.id) :
    F.det = (F.restrict hU).det := by
  rw [LinearMap.det_eq_det_mul_det U F hU, hquot, LinearMap.det_id, mul_one]

/-- Volume preservation on a kernel and the identity action on its quotient
force the full determinant to have absolute value one. -/
theorem abs_det_eq_one_of_kernel_volume (U : Submodule ℝ V)
    (F : V →ₗ[ℝ] V) (hF : F.det ≠ 0) (hU : U ≤ U.comap F)
    (hquot : U.mapQ U F hU = LinearMap.id)
    {n : ℕ} (b : Module.Basis (Fin n) ℝ U)
    (hvol : MeasurePreserving (b.equivFun.conj (F.restrict hU)) volume volume) :
    |F.det| = 1 := by
  have he := det_eq_restrict_of_quotient_eq_id U F hU hquot
  have hb : (b.equivFun.conj (F.restrict hU)).det = (F.restrict hU).det := by
    rw [LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj]
  have hd : (b.equivFun.conj (F.restrict hU)).det ≠ 0 := by
    simpa only [hb, ← he] using hF
  have h := abs_det_eq_one_of_measurePreserving_linearMap _ hd hvol
  simpa only [hb, ← he] using h

end PolycyclicRecognition

end

end OAI
