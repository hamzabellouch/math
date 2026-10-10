import OAI.NumberTheory.PiExponent.Ampleness.AdmissibleCurveModelDegrees

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupMargin
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AdmissibleBlowupGeometry CurveNormalizationModel
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem affineCurveDegreeData (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) :
    Nonempty (AffineCurveDegreeData d C) := by
  obtain ⟨r⟩ := AdmissibleCurveModel.existsModelData d C hn hm
  exact ⟨AdmissibleCurveModel.degreeData d C r⟩

end PiExponent.AdmissibleBlowupMargin

namespace PiExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem uniform_curve_margin :
    ∀ C : NumericalAmpleness.IntegralCurve (blowup d),
      uniformMargin d * (NumericalAmpleness.curveDegree (structureMap d) (H d) C : ℝ) ≤
        (NumericalAmpleness.curveDegree (structureMap d) (interpolationBundle d) C : ℝ) :=
  uniform_curve_margin_of_affine_curve_data d (AdmissibleBlowupMargin.affineCurveDegreeData d)

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
