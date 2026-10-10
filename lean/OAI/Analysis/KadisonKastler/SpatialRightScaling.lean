import OAI.Analysis.KadisonKastler.SpatialStateScaling
import OAI.Analysis.KadisonKastler.SpatialRightSlice

namespace OAI

/-! # State scaling in an arbitrary second tensor leg -/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
theorem productVectorState_right_slice (Ω : H) (ξ : K)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :
    productVectorState (tensorVector ξ Ω) T=productVectorState ξ (rightTensorSlice Ω T) := by
  exact ((leftTensorVector Ω).adjoint_inner_right ξ (T (leftTensorVector Ω ξ))).symm

theorem rightTensorSlice_mul_left (Ω : H) (a : K →L[ℂ] K)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :
    rightTensorSlice Ω (spatialRight a*T)=a*rightTensorSlice Ω T := by
  ext ξ
  exact congrArg (fun V : SpatialHilbert H K →L[ℂ] K => V (T (leftTensorVector Ω ξ)))
    (leftTensorVector_adjoint_spatialRight Ω a)

theorem rightTensorSlice_mul_right (Ω : H) (a : K →L[ℂ] K)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :
    rightTensorSlice Ω (T*spatialRight a)=rightTensorSlice Ω T*a := by
  ext ξ
  change (leftTensorVector Ω).adjoint (T (spatialRight a (leftTensorVector Ω ξ)))=
    (leftTensorVector Ω).adjoint (T (leftTensorVector Ω (a ξ)))
  rw [show spatialRight a (leftTensorVector Ω ξ)=leftTensorVector Ω (a ξ) from
    congrArg (fun V : K →L[ℂ] SpatialHilbert H K => V ξ)
      (spatialRight_leftTensorVector Ω a)]

theorem StateScales.spatialRight {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
    {Ω : H} {ξ : K} {r : ℝ} {a : K →L[ℂ] K}
    (ha : StateScales N ξ r a) :
    StateScales (spatialProductAlgebra M N) (tensorVector ξ Ω) r (spatialRight a) := by
  intro T hT
  rw [productVectorState_right_slice,productVectorState_right_slice,
    rightTensorSlice_mul_right,rightTensorSlice_mul_left]
  exact ha _ (rightTensorSlice_mem M N Ω T hT)

end

end KadisonKastler

end OAI
