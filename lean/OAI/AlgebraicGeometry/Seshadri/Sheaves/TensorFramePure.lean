import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorDivision
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorRestrictPure
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorUnitPure

namespace OAI


                                         
section

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma framed_pure {M N : X.Modules} (e : M ≅ O X) (d : N ≅ O X) (U : X.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorIso e d ≪≫ moduleTensorUnit (O X)).hom.app U (pure M N U m n) =
      (show Γ(X,U) from e.hom.app U m) * (show Γ(X,U) from d.hom.app U n) := by
  change (moduleTensorUnit (O X)).hom.app U ((moduleTensorMap e.hom d.hom).app U
    (pure M N U m n)) = _
  exact (congrArg (fun tensorSection => (moduleTensorUnit (O X)).hom.app U tensorSection)
    (map_pure e.hom d.hom U m n)).trans
      (unit_pure (O X) U (e.hom.app U m) (d.hom.app U n))

lemma local_framed_pure (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (V : U.toScheme.Opens) (m : L.sheaf.val.obj (op (U.ι ''ᵁ V)))
    (n : M.sheaf.val.obj (op (U.ι ''ᵁ V))) :
    (tensorFrame L M U e d).hom.app V (pure L.sheaf M.sheaf (U.ι ''ᵁ V) m n) =
      (show Γ(U.toScheme,V) from e.hom.app V m) * (show Γ(U.toScheme,V) from d.hom.app V n) := by
  change (moduleTensorIso e d ≪≫ moduleTensorUnit (O U.toScheme)).hom.app V
    ((moduleTensorRestrict U L.sheaf M.sheaf).hom.app V
      (pure L.sheaf M.sheaf (U.ι ''ᵁ V) m n)) = _
  exact (congrArg (fun tensorSection =>
    (moduleTensorIso e d ≪≫ moduleTensorUnit (O U.toScheme)).hom.app V tensorSection)
    (restrict_pure U L.sheaf M.sheaf V m n)).trans (framed_pure e d V m n)

end
end MaximalSeshadri.TensorPure

end


end OAI
