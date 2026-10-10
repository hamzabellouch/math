import OAI.Analysis.Pureness.States.ScalarTracialUltraproductTrace
import OAI.Analysis.Pureness.Comparison.FaithfulGNS

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped InnerProductSpace
variable (U : Ultrafilter ℕ)

abbrev ScalarMatrixUltraHilbert := (scalarMatrixUltraTracialState U).functional.GNS

def scalarMatrixUltraGNS : ScalarTracialMatrixUltraproduct U →⋆ₐ[ℂ]
    (ScalarMatrixUltraHilbert U →L[ℂ] ScalarMatrixUltraHilbert U) :=
  (scalarMatrixUltraTracialState U).functional.gnsStarAlgHom

theorem scalarMatrixUltraGNS_injective : Function.Injective (scalarMatrixUltraGNS U) :=
  CuntzComparison.faithful_gns_injective (scalarMatrixUltraTracialState U).functional
    (fun a ha => (scalarMatrixUltraTracialState_faithful U a).mp ha)

theorem scalarMatrixUltraGNS_isometry : Isometry (scalarMatrixUltraGNS U) :=
  NonUnitalStarAlgHom.isometry (scalarMatrixUltraGNS U).toNonUnitalStarAlgHom
    (scalarMatrixUltraGNS_injective U)

theorem scalarMatrixUltraGNS_norm (a : ScalarTracialMatrixUltraproduct U) :
    ‖scalarMatrixUltraGNS U a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (scalarMatrixUltraGNS U).toNonUnitalStarAlgHom
    (scalarMatrixUltraGNS_injective U) a
end CuntzPureness

end

end OAI
