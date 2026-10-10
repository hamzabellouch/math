import OAI.Analysis.LipschitzHilbert.Fourier.LineConjugationBound

namespace OAI

/-! The composition commutator for actual compact smooth directions. -/
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal
namespace LipschitzHilbert.PacketRepresentation

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
  (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
  (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

include hc hcompact in
theorem lineSamplingInverseL2_forward (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) :
    lineSamplingInverseL2Path u hu B hB hb t
      (lineSamplingL2Path u hu t (f.toLp 2 volume))=f.toLp 2 volume := by
  rw [lineSamplingL2Path_onSchwartz u hu hc hcompact]
  simp only [lineSamplingPath,dite_eq_left ht]
  rw [lineSamplingInverseL2Path_onSchwartz u hu hc hcompact B hB hb]
  simp only [lineSamplingInversePath,dite_eq_left ht,lineSamplingInverseSchwartz_forward]

include hc hcompact B hB hb in
theorem compactCompositionCommutator_schwartz (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (t : ℝ) (ht : |t|≤1/4) (f : SchwartzMap ℝ ℂ) :
    ‖lineL2Projection m 1 (by norm_num) (lineSamplingL2Path u hu t (f.toLp 2 volume))-
      lineSamplingL2Path u hu t (lineL2Projection m 1 (by norm_num) (f.toLp 2 volume))‖≤
        16*lineCommutatorNormConstant*A*|t| *‖f.toLp 2 volume‖ := by
  have ht' : |t|≤1/2 := ht.trans (by norm_num)
  let F := lineSamplingSchwartz u hu hc hcompact t ht' f
  have hF : F.toLp 2 volume=lineSamplingL2Path u hu t (f.toLp 2 volume) := by
    rw [lineSamplingL2Path_onSchwartz u hu hc hcompact]
    simp only [lineSamplingPath,dite_eq_left ht',F]
  have hi := lineSamplingInverseL2_forward u hu hc hcompact B hB hb t ht' f
  have hFnorm : ‖F.toLp 2 volume‖≤2*‖f.toLp 2 volume‖ := by
    rw [hF]
    exact ((lineSamplingL2Path u hu t).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (lineSamplingL2Path_bound u hu t) (norm_nonneg _))
  have hh := lineConjugation_difference_bound u hu hc hcompact B hB hb m A hA hm t ht F
  have he : lineConjugationL2 u hu B hB hb m t (F.toLp 2 volume)=
      lineSamplingL2Path u hu t (lineL2Projection m 1 (by norm_num) (f.toLp 2 volume)) := by
    simp only [lineConjugationL2,ContinuousLinearMap.comp_apply,hF,hi]
  rw [he,hF,norm_sub_rev] at hh
  rw [hF] at hFnorm
  apply hh.trans
  calc
    _ ≤ 8*lineCommutatorNormConstant*A*|t| *(2*‖f.toLp 2 volume‖) :=
      mul_le_mul_of_nonneg_left hFnorm (by have := lineCommutatorNormConstant_nonneg; positivity)
    _ = _ := by ring

include hc hcompact B hB hb in
theorem compactCompositionCommutator_L2 (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (t : ℝ) (ht : |t|≤1/4) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖lineL2Projection m 1 (by norm_num) (lineSamplingL2Path u hu t f)-
      lineSamplingL2Path u hu t (lineL2Projection m 1 (by norm_num) f)‖≤
        16*lineCommutatorNormConstant*A*|t| *‖f‖ := by
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  refine hd.induction_on f (isClosed_le (by fun_prop) (by fun_prop)) ?_
  exact compactCompositionCommutator_schwartz u hu hc hcompact B hB hb m A hA hm t ht

end LipschitzHilbert.PacketRepresentation

end

end OAI
