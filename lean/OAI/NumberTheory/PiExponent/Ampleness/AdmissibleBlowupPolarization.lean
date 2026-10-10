import OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin
import OAI.NumberTheory.PiExponent.Ampleness.BlowupAmpleTwist

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem exists_ampleExponent : ∃ a : ℕ, 1 < a ∧ (((A d).pow a).tensor (J d)).IsAmple :=
  PiExponentSeshadri.BlowupGluing.exists_ample_exceptional_power_gt_one
    (centerIdeal d) (centerIdeal_support_ne_top d) (hyperplane d) (hyperplane_ample d)

def ampleExponent : ℕ := (exists_ampleExponent d).choose

theorem ampleExponent_gt_one : 1 < ampleExponent d := (exists_ampleExponent d).choose_spec.1

def H : LineBundle (blowup d) := ((A d).pow (ampleExponent d)).tensor (J d)

theorem H_ample : (H d).IsAmple := (exists_ampleExponent d).choose_spec.2

def interpolationBundle : LineBundle (blowup d) := (A d).tensor (J d)

def uniformMargin : ℝ := BlowupCurveMargin.marginCoefficient (ampleExponent d) d.sigma

theorem uniformMargin_pos : 0 < uniformMargin d :=
  BlowupCurveMargin.marginCoefficient_pos (ampleExponent_gt_one d) d.sigma_pos

theorem uniform_curve_margin_of_affine_curve_data
    (hdata : ∀ C : IntegralCurve (blowup d),
      (¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ ({x} : Set _)) →
      (∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) →
      Nonempty (AdmissibleBlowupMargin.AffineCurveDegreeData d C)) :
    ∀ C : IntegralCurve (blowup d),
      uniformMargin d * (curveDegree (structureMap d) (H d) C : ℝ) ≤
        (curveDegree (structureMap d) (interpolationBundle d) C : ℝ) :=
  AdmissibleBlowupMargin.uniform_margin_of_affine_curve_data d (ampleExponent d)
    (ampleExponent_gt_one d) (H_ample d) hdata

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
