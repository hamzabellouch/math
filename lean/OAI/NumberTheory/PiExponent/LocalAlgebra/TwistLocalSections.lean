import OAI.NumberTheory.PiExponent.Approximation.TwistSections

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X : Scheme.{0}}

theorem moduleTwist_app_bijective (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    {M N : X.Modules} (β : M ⟶ N) (n : ℕ)
    (h : Function.Bijective (β.app U)) :
    Function.Bijective (((moduleTwistFunctor L n).map β).app U) := by
  let E := SheafOfModules.evaluation U.toScheme.ringCatSheaf (op (⊤ : U.toScheme.Opens))
  have he := NatIso.isIso_map_iff
    (Functor.isoWhiskerRight (moduleTwistRestrictFrame L U e n) E) β
  have hright : IsIso (((Scheme.Modules.restrictFunctor U.ι) ⋙ E).map β) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (β.app (U.ι ''ᵁ ⊤))
    exact U.ι_image_top.symm ▸ h
  have hleft := he.mpr hright
  have hb := ConcreteCategory.bijective_of_isIso
    ((((moduleTwistFunctor L n ⋙ Scheme.Modules.restrictFunctor U.ι) ⋙ E).map β))
  change Function.Bijective (((moduleTwistFunctor L n).map β).app (U.ι ''ᵁ ⊤)) at hb
  exact U.ι_image_top ▸ hb

end
end PiExponentSeshadri.Geometry

end OAI
