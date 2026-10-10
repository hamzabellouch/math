import OAI.Analysis.LipschitzHilbert.Fourier.LineSamplingStrongDerivative

namespace OAI

/-! Bounded L2 sampling paths and their agreement with the Schwartz paths. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
  (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
  (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

def lineSamplingL2Path (s : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  if hs : |s|≤1/2 then lineCompositionL2 (lineSampling u s)
    (lineSampling_lipschitz u hu s hs).continuous.measurable (lineSampling_antilipschitz u hu s hs)
  else ContinuousLinearMap.id ℂ _

def lineSamplingInverseL2Path (s : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  if hs : |s|≤1/2 then lineCompositionL2 (lineSamplingInverse u s)
    (lineSamplingInverse_space_lipschitz u hu B hB hb s hs).continuous.measurable
    (lineSamplingInverse_antilipschitz u hu B hB hb s hs)
  else ContinuousLinearMap.id ℂ _

theorem lineSamplingL2Path_onSchwartz (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    lineSamplingL2Path u hu s (f.toLp 2 volume)=
      (lineSamplingPath u hu hc hcompact s f).toLp 2 volume := by
  by_cases hs : |s|≤1/2
  · simp only [lineSamplingL2Path,lineSamplingPath,dite_eq_left hs]
    exact lineCompositionL2_schwartz _ (lineSampling_temperate u hc hcompact s) _ f
  · simp only [lineSamplingL2Path,lineSamplingPath,dite_eq_right hs,ContinuousLinearMap.id_apply]

theorem lineSamplingInverseL2Path_onSchwartz (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    lineSamplingInverseL2Path u hu B hB hb s (f.toLp 2 volume)=
      (lineSamplingInversePath u hu hc hcompact B hB hb s f).toLp 2 volume := by
  by_cases hs : |s|≤1/2
  · simp only [lineSamplingInverseL2Path,lineSamplingInversePath,dite_eq_left hs]
    exact lineCompositionL2_schwartz _ (lineSamplingInverse_temperate u hu hc hcompact B hB hb s hs) _ f
  · simp only [lineSamplingInverseL2Path,lineSamplingInversePath,dite_eq_right hs,ContinuousLinearMap.id_apply]

theorem lineSamplingL2Path_bound (s : ℝ) : ‖lineSamplingL2Path u hu s‖≤2 := by
  by_cases hs : |s|≤1/2
  · simp only [lineSamplingL2Path,dite_eq_left hs]
    exact lineCompositionL2_bound _ _ _
  · simp only [lineSamplingL2Path,dite_eq_right hs]
    exact (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure ℝ))‖≤1).trans (by norm_num)

theorem lineSamplingInverseL2Path_bound (s : ℝ) : ‖lineSamplingInverseL2Path u hu B hB hb s‖≤2 := by
  by_cases hs : |s|≤1/2
  · simp only [lineSamplingInverseL2Path,dite_eq_left hs]
    exact lineCompositionL2_bound _ _ _
  · simp only [lineSamplingInverseL2Path,dite_eq_right hs]
    exact (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure ℝ))‖≤1).trans (by norm_num)

theorem lineSamplingTangent_eq (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) :
    lineSamplingTangent u hu hc hcompact t ht f=
      lineSamplingSchwartz u hu hc hcompact t ht
        (lineSchwartzProduct (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht)
          (schwartzDerivative 1 f)) := by
  ext y
  have he : (lineSamplingHomeomorph u hu B hB hb t ht).symm (lineSampling u t y)=y :=
    (lineSamplingHomeomorph u hu B hB hb t ht).symm_apply_apply y
  simp only [lineSamplingTangent_apply,lineSamplingSchwartz_apply,lineSchwartzProduct_apply,
    schwartzDerivative_one_apply,lineSamplingGeneratorSchwartz_apply,lineSamplingGenerator,
    he,Complex.ofReal_neg,neg_smul,Complex.real_smul,neg_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
