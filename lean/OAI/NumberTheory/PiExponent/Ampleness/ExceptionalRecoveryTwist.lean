import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryMap
import OAI.NumberTheory.PiExponent.LocalAlgebra.TwistLocalSections

namespace OAI

namespace PiExponent.GeometrySupport.ExceptionalRecoveryMap
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
variable {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (E : LineBundle Y)
    (ι : E.sheaf ⟶ structureSheaf Y) (hE : PresentsPullbackIdeal I f E ι)

theorem twistedMap_app_bijective (A : LineBundle X) (n : ℕ) (U : X.Opens)
    (e : A.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (h : Function.Bijective ((ordinaryMap f I E ι hE n).app U)) :
    Function.Bijective ((twistedMap f I E ι hE A n).app U) := by
  let a := (ProjectionFormula.twistIso f (modulePow Y E.sheaf n) A n).symm ≪≫
    (Scheme.Modules.pushforward f).mapIso
      (moduleTwistPowerIso (A.pullback f) (modulePow Y E.sheaf n) n ≪≫
        (lineTensorPow E (A.pullback f) n).symm)
  let : IsIso ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map a.hom) :=
    ((SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso a).isIso_hom
  have ha := ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map a.hom)
  exact ha.comp (moduleTwist_app_bijective A U e (ordinaryMap f I E ι hE n) n h)

end
end PiExponent.GeometrySupport.ExceptionalRecoveryMap

end OAI
