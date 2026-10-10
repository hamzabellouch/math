import OAI.Geometry.Immersion.ClosedSurface.QuadraticMean
import OAI.Geometry.Immersion.ClosedSurface.NormalFrame

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes Set


def phaseCoframe (ξ : Base) : Base →ₗ[ℝ] Base where
  toFun p := (ξ.1 * p.1 + ξ.2 * p.2, -ξ.2 * p.1 + ξ.1 * p.2)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring

def phaseCoframeInv (ξ : Base) : Base →ₗ[ℝ] Base where
  toFun p := ((ξ.1 * p.1 - ξ.2 * p.2) / (ξ.1^2 + ξ.2^2),
    (ξ.2 * p.1 + ξ.1 * p.2) / (ξ.1^2 + ξ.2^2))
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring

lemma covector_length_sq_pos {ξ : Base} (hξ : ξ ≠ 0) : 0 < ξ.1^2 + ξ.2^2 := by
  by_contra h
  have ha : ξ.1 = 0 := by nlinarith [sq_nonneg ξ.1, sq_nonneg ξ.2]
  have hb : ξ.2 = 0 := by nlinarith [sq_nonneg ξ.1, sq_nonneg ξ.2]
  exact hξ (Prod.ext ha hb)

lemma phaseCoframe_left_inv {ξ : Base} (hξ : ξ ≠ 0) :
    Function.LeftInverse (phaseCoframeInv ξ) (phaseCoframe ξ) := by
  intro p
  have hd := (covector_length_sq_pos hξ).ne'
  ext <;> simp only [phaseCoframe, phaseCoframeInv, LinearMap.coe_mk, AddHom.coe_mk] <;>
    field_simp <;> ring

lemma phaseCoframe_right_inv {ξ : Base} (hξ : ξ ≠ 0) :
    Function.RightInverse (phaseCoframeInv ξ) (phaseCoframe ξ) := by
  intro p
  have hd := (covector_length_sq_pos hξ).ne'
  ext <;> simp only [phaseCoframe, phaseCoframeInv, LinearMap.coe_mk, AddHom.coe_mk] <;>
    field_simp <;> ring

def phaseEquiv (ξ : Base) (hξ : ξ ≠ 0) : Base ≃L[ℝ] Base :=
  (LinearEquiv.ofLinearMap (phaseCoframe ξ) (phaseCoframeInv ξ)
    (LinearMap.ext (phaseCoframe_right_inv hξ))
    (LinearMap.ext (phaseCoframe_left_inv hξ))).toContinuousLinearEquiv

@[simp] lemma phaseEquiv_apply (ξ : Base) (hξ : ξ ≠ 0) (p : Base) :
    phaseEquiv ξ hξ p = (ξ.1 * p.1 + ξ.2 * p.2, -ξ.2 * p.1 + ξ.1 * p.2) := rfl

@[simp] lemma phaseEquiv_symm_apply (ξ : Base) (hξ : ξ ≠ 0) (p : Base) :
    (phaseEquiv ξ hξ).symm p = ((ξ.1 * p.1 - ξ.2 * p.2) / (ξ.1^2 + ξ.2^2),
      (ξ.2 * p.1 + ξ.1 * p.2) / (ξ.1^2 + ξ.2^2)) := rfl


theorem exists_phase_complement {ξ : Base} (hξ : ξ ≠ 0) :
    ∃ χ : Base ≃L[ℝ] Base,
      (∀ p, (χ p).1 = ξ.1 * p.1 + ξ.2 * p.2) ∧
      χ.symm (0,1) = (ξ.1^2 + ξ.2^2)⁻¹ • (-ξ.2, ξ.1) := by
  refine ⟨phaseEquiv ξ hξ, fun p => rfl, ?_⟩
  ext <;> simp [div_eq_mul_inv, mul_comm]

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
