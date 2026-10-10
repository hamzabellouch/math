import OAI.Analysis.Nuclearity.PureProductRepresentation
import OAI.Analysis.Nuclearity.ProductPureSeparation

namespace OAI

/-! Product pure-state functionals realized in the faithful product representation. -/

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder
open UniformSpace

namespace WeakPureInfiniteness

universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

def pureProductVector (f : PureStateData A) (g : PureStateData B) :
    (pureProductRepresentation (A := A) (B := B)).space :=
  ((pureCyclicVector f ⊗ₜ[ℂ] pureCyclicVector g :
    pureGNSHilbert A ⊗[ℂ] pureGNSHilbert B) : Completion _)

@[simp] theorem norm_pureProductVector (f : PureStateData A) (g : PureStateData B) :
    ‖pureProductVector f g‖ = 1 := by
  simp only [pureProductVector, Completion.norm_coe, TensorProduct.norm_tmul,
    norm_pureCyclicVector, one_mul]

def pureProductCoefficient (f : PureStateData A) (g : PureStateData B) :
    MinimalTensor A B →L[ℂ] ℂ :=
  (spatialVectorFunctional pureProductRepresentation (pureProductVector f g)).comp
    (minimalTensorSubalgebra A B).toNonUnitalSubalgebra.toSubmodule.subtypeL

@[simp] theorem pureProductCoefficient_apply (f : PureStateData A) (g : PureStateData B)
    (z : MinimalTensor A B) :
    pureProductCoefficient f g z = inner ℂ (pureProductVector f g)
      (minimalSpatialEvaluation pureProductRepresentation z (pureProductVector f g)) := rfl

theorem pureProductCoefficient_norm (f : PureStateData A) (g : PureStateData B) :
    ‖pureProductCoefficient f g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  calc
    _ ≤ ‖spatialVectorFunctional pureProductRepresentation (pureProductVector f g)‖ * ‖z.val‖ :=
      (spatialVectorFunctional pureProductRepresentation (pureProductVector f g)).le_opNorm z.val
    _ ≤ (‖pureProductVector f g‖ * ‖pureProductVector f g‖) * ‖z.val‖ :=
      mul_le_mul_of_nonneg_right (norm_spatialVectorFunctional_le _ _) (norm_nonneg _)
    _ = 1 * ‖z‖ := by simp only [norm_pureProductVector, one_mul]; rfl

theorem pureProductCoefficient_elementary (f : PureStateData A) (g : PureStateData B)
    (a : A) (b : B) :
    pureProductCoefficient f g (minimalElementary a b) = f.state a * g.state b := by
  change spatialVectorFunctional pureProductRepresentation (pureProductVector f g)
    (spatialElementary a b) = _
  rw [pureProductVector, spatialVectorFunctional_elementary]
  simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul]
  change inner ℂ (pureCyclicVector f) (pureGNSRepresentation A a (pureCyclicVector f)) *
    inner ℂ (pureCyclicVector g) (pureGNSRepresentation B b (pureCyclicVector g)) = _
  have hA : inner ℂ (pureCyclicVector f)
      (pureGNSRepresentation A a (pureCyclicVector f)) = f.state a := by
    rw [pureCyclicVector, pureGNSRepresentation_single]
    exact (pureGNS_inner_single f _ _).trans (Pureness.stateGNS_vector_value f.state a)
  have hB : inner ℂ (pureCyclicVector g)
      (pureGNSRepresentation B b (pureCyclicVector g)) = g.state b := by
    rw [pureCyclicVector, pureGNSRepresentation_single]
    exact (pureGNS_inner_single g _ _).trans (Pureness.stateGNS_vector_value g.state b)
  exact congrArg₂ (· * ·) hA hB

def faithfulPureProductFunctional (f : PureStateData A) (g : PureStateData B) :
    ProductPureFunctional A B where
  leftState := f.state
  rightState := g.state
  left_one := f.unital
  right_one := g.unital
  left_pure := f.pure
  right_pure := g.pure
  functional := pureProductCoefficient f g
  norm_le_one := pureProductCoefficient_norm f g
  elementary := pureProductCoefficient_elementary f g

end WeakPureInfiniteness

end

end OAI
