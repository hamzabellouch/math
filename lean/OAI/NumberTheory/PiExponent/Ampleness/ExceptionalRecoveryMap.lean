import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerPresentation
import OAI.NumberTheory.PiExponent.Ampleness.LineAmpleOperations
import OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws
import OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap

namespace OAI

namespace PiExponent.GeometrySupport.ExceptionalRecoveryMap
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
variable {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (E : LineBundle Y)
    (ι : E.sheaf ⟶ structureSheaf Y) (hE : PresentsPullbackIdeal I f E ι)

def ordinaryMap (n : ℕ) : closedModule (I^n) ⟶
    (Scheme.Modules.pushforward f).obj (modulePow Y E.sheaf n) :=
  IdealPullbackMap.comap f (I^n) ≫
    (Scheme.Modules.pushforward f).map (PresentedIdealIso.powerIso I f E ι hE n).inv

@[reassoc (attr := simp)] theorem ordinaryMap_inclusion (n : ℕ) :
    ordinaryMap f I E ι hE n ≫
      (Scheme.Modules.pushforward f).map (idealPowerInclusion E ι n) =
    closedInclusion (I^n) ≫ structureMap f := by
  have he : (PresentedIdealIso.powerIso I f E ι hE n).inv ≫
      idealPowerInclusion E ι n = closedInclusion ((I^n).comap f) := by
    rw [← PresentedIdealIso.powerIso_hom_inclusion I f E ι hE n]
    exact Iso.inv_hom_id_assoc _ _
  rw [ordinaryMap, Category.assoc]
  erw [← Functor.map_comp, he]
  exact IdealPullbackMap.comap_inclusion f (I^n)

theorem ordinaryMap_app_inclusion (n : ℕ) (U : X.Opens) (s : Γ(closedModule (I^n), U)) :
    (idealPowerInclusion E ι n).app (f ⁻¹ᵁ U)
      ((ordinaryMap f I E ι hE n).app U s) =
    f.app U ((closedInclusion (I^n)).app U s) :=
  congrArg (fun g => g.app U s) (ordinaryMap_inclusion f I E ι hE n)

def twistedMap (A : LineBundle X) (n : ℕ) :
    (moduleTwistFunctor A n).obj (closedModule (I^n)) ⟶
      (Scheme.Modules.pushforward f).obj ((E.tensor (A.pullback f)).pow n).sheaf :=
  (moduleTwistFunctor A n).map (ordinaryMap f I E ι hE n) ≫
    (ProjectionFormula.twistIso f (modulePow Y E.sheaf n) A n).inv ≫
      (Scheme.Modules.pushforward f).map
        ((moduleTwistPowerIso (A.pullback f) (modulePow Y E.sheaf n) n).hom ≫
          (lineTensorPow E (A.pullback f) n).inv)

end
end PiExponent.GeometrySupport.ExceptionalRecoveryMap

end OAI
