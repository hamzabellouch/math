import OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupAmple
import OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupJetSurjectivity

namespace OAI

namespace PiExponent.AdmissibleJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.AdmissibleBlowupGeometry PiExponent.BlowupJetSurjectivity
attribute [local irreducible] AdmissibleBlowupGeometry.centerIdeal
  AdmissibleBlowupGeometry.hyperplane
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem blowupBundle_ample :
    (blowupBundle (centerIdeal d) (hyperplane d)).IsAmple := by
  apply PiExponent.AmpleIso.isAmple_of_sheaf_iso (interpolationBundle d)
    (blowupBundle (centerIdeal d) (hyperplane d))
    (moduleTensorComm (A d).sheaf (J d).sheaf)
  exact interpolationBundle_ample d

end
end PiExponent.AdmissibleJetSurjectivity

end OAI
