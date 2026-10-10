import OAI.Analysis.Mahler.SourceRawJets
import OAI.Analysis.Mahler.RawAlternationDerivative

namespace OAI

namespace Mahler
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def rawLinearJet (A : E →L[ℝ] E →L[ℝ] ℂ) : E →ₗ[ℝ] E →ₗ[ℝ] ℂ where
  toFun v := (A v).toLinearMap
  map_add' v w := by ext z; simp
  map_smul' r v := by ext z; simp

lemma rawCovector_hasRawFDerivAt {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) :
    HasRawFDerivAt (fun y => rawCovector (a y).toLinearMap)
      (rawCovectorVariation (rawLinearJet (fderiv ℝ a x))) x := by
  intro v
  have hd := ha.hasFDerivAt.clm_apply (hasFDerivAt_const (v 0) x)
  apply hd.congr_fderiv
  ext w
  simp [rawCoefficientDerivative_apply, rawCovectorVariation, rawLinearJet]

lemma rawFirstJet_hasRawFDerivAt {A : E → E →L[ℝ] E →L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) :
    HasRawFDerivAt (fun y => rawFirstJet (A y)) (rawSecondJet (fderiv ℝ A x)) x := by
  intro v
  have hd := (hA.hasFDerivAt.clm_apply (hasFDerivAt_const (v 0) x)).clm_apply
    (hasFDerivAt_const (v 1) x)
  apply hd.congr_fderiv
  ext w
  simp [rawCoefficientDerivative_apply]

/-- The coefficientwise derivative of the full raw
form, including every derivative of every first-jet factor. -/
theorem rawBoundary_hasRawFDerivAt {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (k : ℕ) :
    HasRawFDerivAt
      (fun y => rawBoundary (a y).toLinearMap (rawFirstJet (fderiv ℝ a y)) k)
      (rawProductVariation (rawCovector (a x).toLinearMap)
        (rawCovectorVariation (rawLinearJet (fderiv ℝ a x)))
        (rawPower (rawFirstJet (fderiv ℝ a x)) k)
        (rawPowerVariation (rawFirstJet (fderiv ℝ a x))
          (rawSecondJet (fderiv ℝ (fderiv ℝ a) x)) k)) x := by
  have hda : ContDiffAt ℝ 1 (fderiv ℝ a) x := ha.fderiv_right (by norm_num)
  exact (rawCovector_hasRawFDerivAt (ha.differentiableAt (by norm_num))).product
    ((rawFirstJet_hasRawFDerivAt (hda.differentiableAt one_ne_zero)).power k)

end
end Mahler

end OAI
