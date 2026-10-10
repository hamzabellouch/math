import OAI.NumberTheory.PiExponent.Approximation.InverseFrames
import OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse

namespace OAI

namespace PiExponent.InverseFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}} {M N : X.Modules}

lemma dualMap_restrict (E : moduleTensor X M N ≅ O X) (s : O X ⟶ M) (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).map (dualMap E s) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom =
    dualMap (restrictPairing E U) (restrictSection U.ι s) := by
  ext A n
  change Γ(N, U.ι ''ᵁ A) at n
  change (U.ι.appIso A).hom ((dualMap E s).app (U.ι ''ᵁ A) n) =
    (dualMap (restrictPairing E U) (restrictSection U.ι s)).app A n
  erw [dualMap_apply E s (U.ι ''ᵁ A) n,
    dualMap_apply (restrictPairing E U) (restrictSection U.ι s) A n]
  change (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A)
        (s.app (U.ι ''ᵁ A) (1 : Γ(X,U.ι ''ᵁ A))) n)) =
    (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      ((moduleTensorRestrict U M N).inv.app A
        (PiExponentSeshadri.TensorPure.pure (M.restrict U.ι) (N.restrict U.ι) A
          ((restrictSection U.ι s).app A (1 : Γ(U.toScheme,A))) n)))
  erw [restrict_pure_inv U M N A
    ((restrictSection U.ι s).app A (1 : Γ(U.toScheme,A))) n]
  change (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A)
        (s.app (U.ι ''ᵁ A) (1 : Γ(X,U.ι ''ᵁ A))) n)) =
    (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A)
        (s.app (U.ι ''ᵁ A) ((U.ι.appIso A).inv (1 : Γ(U.toScheme,A)))) n))
  rw [show (U.ι.appIso A).inv (1 : Γ(U.toScheme,A)) = (1 : Γ(X,U.ι ''ᵁ A)) from
    (U.ι.appIso A).inv.hom.map_one]

lemma dualMap_restrict_coefficient (E : moduleTensor X M N ≅ O X)
    (s : O X ⟶ M) (U : X.Opens) (e : M.restrict U.ι ≅ O U.toScheme) :
    endValue ((inverseOpenFrame E U e).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (dualMap E s) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom) =
    coefficient e (restrictSection U.ι s) := by
  erw [dualMap_restrict]
  exact dualMap_coefficient (restrictPairing E U) e (restrictSection U.ι s)

lemma dualSection_restrict_coefficient (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    endValue ((inverseOpenFrame (lineTensorInverseIso L) U e).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (L.dualSection s) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom) =
    coefficient e (restrictSection U.ι s) :=
  dualMap_restrict_coefficient (lineTensorInverseIso L) s U e

end
end PiExponent.InverseFrames

end OAI
