import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorOpenSquare

namespace OAI


                                           
section

namespace MaximalSeshadri.OpenBaseChange
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.TensorPure

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

@[reassoc] lemma naturality {M N : X.Modules} (a : M ⟶ N) :
    (Scheme.Modules.restrictFunctor U.ι).map ((Scheme.Modules.pushforward f).map a) ≫
      (iso f U N).hom =
    (iso f U M).hom ≫ (Scheme.Modules.pushforward (f ∣_ U)).map
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map a) := by
  ext V x
  change (hom f U N).app V (a.app (f ⁻¹ᵁ (U.ι ''ᵁ V)) x) =
    a.app ((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) ((hom f U M).app V x)
  rw [hom_app,hom_app]
  exact (CategoryTheory.congr_fun (a.mapPresheaf.naturality
    (eqToHom (image_morphismRestrict_preimage f U V)).op) x).symm

end
end MaximalSeshadri.OpenBaseChange

end



end OAI
