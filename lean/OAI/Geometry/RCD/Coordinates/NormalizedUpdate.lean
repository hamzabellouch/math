import OAI.Geometry.RCD.Coordinates.FrozenJetTransport
import OAI.Geometry.RCD.Sobolev.MetricCoercivity

namespace OAI

/-!
# The coordinate update in frozen coordinates

The source coordinate and its dual covector are transformed together.
Consequently the inverse-transpose update has exactly the same form in
the normalized variables; no norm of the coordinate change occurs.
-/

open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Affine coordinates frozen at a point and a scale. -/
def frozenSource (r : ℝ) (T : E ≃L[ℝ] E) (x z : E) : E := x + r • T.symm z

/-- The normalized coordinate map, with its value at the center removed. -/
def normalizedCoordinates (r : ℝ) (T : E ≃L[ℝ] E) (x : E) (h : E → E)
    (z : E) : E := r⁻¹ • (h (frozenSource r T x z) - h x)

/-- The covector field uses the dual coordinate change. -/
def normalizedCovector (r : ℝ) (T : E ≃L[ℝ] E) (x : E) (v : E → E)
    (z : E) : E :=
  r⁻¹ • (T.symm : E →L[ℝ] E).adjoint (v (frozenSource r T x z))

omit [CompleteSpace E] in
/-- The scale cancels out of the normalized Jacobian. -/
theorem fderiv_normalizedCoordinates {r : ℝ} (hr : r ≠ 0)
    (T : E ≃L[ℝ] E) (x z : E) (h : E → E)
    (hh : DifferentiableAt ℝ h (frozenSource r T x z)) :
    fderiv ℝ (normalizedCoordinates r T x h) z =
      fderiv ℝ h (frozenSource r T x z) ∘L (T.symm : E →L[ℝ] E) := by
  have hsource : HasFDerivAt (frozenSource r T x)
      (r • (T.symm : E →L[ℝ] E)) z := by
    change HasFDerivAt (fun y => x + r • T.symm y) _ z
    convert (((T.symm : E →L[ℝ] E).hasFDerivAt.const_smul r).const_add x) using 1
    funext y
    rfl
  have hn := ((hh.hasFDerivAt.comp z hsource).sub_const (h x)).const_smul r⁻¹
  change HasFDerivAt (normalizedCoordinates r T x h) _ z at hn
  rw [hn.fderiv]
  ext ξ
  simp [smul_smul, hr]

/-- Exact covariance of the inverse transpose when the covector uses
the dual change of basis. -/
theorem inverseTranspose_normalized_apply (T J : E ≃L[ℝ] E) (w : E) :
    inverseTranspose (T.symm.trans J) ((T.symm : E →L[ℝ] E).adjoint w) =
      inverseTranspose J w := by
  have hinv : ((T.symm.trans J).symm : E →L[ℝ] E) =
      (T : E →L[ℝ] E) ∘L (J.symm : E →L[ℝ] E) := by
    ext y
    rfl
  change ((↑(T.symm.trans J).symm : E →L[ℝ] E).adjoint)
    ((T.symm : E →L[ℝ] E).adjoint w) = inverseTranspose J w
  rw [hinv]
  exact (inverseTranspose_frozen_factor T J w).symm

/-- The actual normalized update is the normalized old map plus its
inverse-transpose correction. Centering at the new map only changes
this expression by a constant, handled by the jet transport lemmas. -/
theorem normalized_update_identity {r : ℝ} (hr : r ≠ 0)
    (T : E ≃L[ℝ] E) (x z : E) (h v : E → E)
    (hh : DifferentiableAt ℝ h (frozenSource r T x z))
    (J : E ≃L[ℝ] E)
    (hJ : fderiv ℝ h (frozenSource r T x z) = (J : E →L[ℝ] E)) :
    r⁻¹ • (h (frozenSource r T x z) +
        operatorInverseTranspose (fderiv ℝ h (frozenSource r T x z))
          (v (frozenSource r T x z)) - h x) =
      normalizedCoordinates r T x h z +
        operatorInverseTranspose (fderiv ℝ (normalizedCoordinates r T x h) z)
          (normalizedCovector r T x v z) := by
  have hnormalized : fderiv ℝ (normalizedCoordinates r T x h) z =
      (T.symm.trans J : E ≃L[ℝ] E) := by
    rw [fderiv_normalizedCoordinates hr T x z h hh, hJ]
    rfl
  rw [hnormalized, hJ, operatorInverseTranspose_equiv, operatorInverseTranspose_equiv]
  unfold normalizedCoordinates normalizedCovector
  rw [map_smul, inverseTranspose_normalized_apply]
  module

end RegularPointCoordinates

end

end OAI
