import OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent
import OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent
import OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace PiExponent.CompactJetIdeal


theorem closedModule_isFinitePresentation {X : Scheme} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) :
    (PiExponentSeshadri.IdealModule.closedModule I).IsFinitePresentation := by
  let : (PiExponentSeshadri.IdealModule.unit X).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : (PiExponentSeshadri.IdealModule.unit I.subscheme).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : ((Scheme.Modules.pushforward I.subschemeι).obj
      (PiExponentSeshadri.IdealModule.unit I.subscheme)).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward I.subschemeι).obj
        (PiExponentSeshadri.IdealModule.unit I.subscheme))).choose.isQuasicoherent
  exact FiniteGlobalPresentation.kernel_isFinitePresentation
    (PiExponentSeshadri.IdealModule.structureMap I.subschemeι)

theorem extend_isFinitePresentation {U X : Scheme} [IsLocallyNoetherian X]
    (I : U.IdealSheafData) (j : U ⟶ X) :
    (PiExponentSeshadri.IdealModule.closedModule (extend I j)).IsFinitePresentation :=
  closedModule_isFinitePresentation (extend I j)

end PiExponent.CompactJetIdeal
end

end OAI
