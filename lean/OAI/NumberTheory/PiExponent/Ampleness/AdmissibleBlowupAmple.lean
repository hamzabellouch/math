import OAI.NumberTheory.PiExponent.Ampleness.NumericalAmplenessTheorem
import OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveDegreeData

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupGeometry
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem interpolationBundle_ample : (interpolationBundle d).IsAmple :=
  NumericalAmpleness.isAmple_of_uniform_curve_margin (structureMap d)
    (H d) (interpolationBundle d) (H_ample d) (uniformMargin d)
    (uniformMargin_pos d) (uniform_curve_margin d)

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
