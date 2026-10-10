import OAI.Analysis.IrrationalRotation.Operators.TracialStateBounds
import OAI.Analysis.IrrationalRotation.Model.OperatorProperties

namespace OAI

noncomputable section
open scoped CStarAlgebra ComplexOrder
namespace Invariant233.TracialState
variable {A : Type*} [CStarAlgebra A]
local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

def gnsVector (τ : TracialState A) : τ.toPositiveLinearMap.GNS :=
  (τ.toPositiveLinearMap.toPreGNS 1 : τ.toPositiveLinearMap.GNS)

theorem gns_apply_vector (τ : TracialState A) (a : A) :
    τ.toPositiveLinearMap.gnsStarAlgHom a (τ.gnsVector) =
      (τ.toPositiveLinearMap.toPreGNS a : τ.toPositiveLinearMap.GNS) := by
  change τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom a
    (τ.toPositiveLinearMap.toPreGNS 1 : τ.toPositiveLinearMap.GNS) = _
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,
    PositiveLinearMap.leftMulMapPreGNS_apply]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, mul_one]

theorem norm_gnsVector (τ : TracialState A) : ‖τ.gnsVector‖ = 1 := by
  rw [gnsVector, UniformSpace.Completion.norm_coe, PositiveLinearMap.preGNS_norm_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul,
    toPositiveLinearMap_apply, τ.map_one, Complex.one_re, Real.sqrt_one]

theorem gns_vectorTrace (τ : TracialState A) (a : A) :
    vectorTrace τ.gnsVector (τ.toPositiveLinearMap.gnsStarAlgHom a) = τ a := by
  unfold vectorTrace
  rw [τ.gns_apply_vector]
  change inner ℂ (τ.toPositiveLinearMap.toPreGNS 1 : τ.toPositiveLinearMap.GNS)
    (τ.toPositiveLinearMap.toPreGNS a : τ.toPositiveLinearMap.GNS) = _
  rw [UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul,
    toPositiveLinearMap_apply]

theorem denseRange_gns_orbit (τ : TracialState A) :
    DenseRange (fun a : A => τ.toPositiveLinearMap.gnsStarAlgHom a τ.gnsVector) := by
  simp_rw [τ.gns_apply_vector]
  exact UniformSpace.Completion.denseRange_coe.comp
    τ.toPositiveLinearMap.toPreGNS.surjective.denseRange (by fun_prop)

end Invariant233.TracialState

end

end OAI
