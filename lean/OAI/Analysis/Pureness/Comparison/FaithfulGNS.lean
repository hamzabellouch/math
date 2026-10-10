import OAI.Analysis.Pureness.Comparison.FaithfulTrace
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI
open scoped ComplexOrder
noncomputable section
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem faithful_gns_injective (f : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, f (star a * a) = 0 → a = 0) :
    Function.Injective f.gnsStarAlgHom := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have hz : (f.toPreGNS a : f.GNS) = 0 := by
    have h := congrArg (fun T : f.GNS →L[ℂ] f.GNS => T (f.toPreGNS 1)) ha
    simpa [PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.leftMulMapPreGNS] using h
  have hn : ‖f.toPreGNS a‖ = 0 := by
    have := congrArg norm hz
    simpa using this
  apply hf a
  have h := f.preGNS_norm_sq (f.toPreGNS a)
  simpa [hn] using h.symm

theorem TracialState.gns_injective [IsSimpleCStarAlgebra A] (τ : TracialState A) :
    Function.Injective τ.toPositiveLinearMap.gnsStarAlgHom :=
  faithful_gns_injective τ.toPositiveLinearMap (fun _ => τ.faithful)

 theorem TracialState.gns_norm [IsSimpleCStarAlgebra A] (τ : TracialState A) (a : A) :
    ‖τ.toPositiveLinearMap.gnsStarAlgHom a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom τ.gns_injective a
end CuntzComparison

end

end OAI
