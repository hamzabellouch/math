import OAI.Analysis.IrrationalRotation.Spectral.DeterminantRegularization
import OAI.Analysis.IrrationalRotation.Spectral.DeterminantHomogeneity

namespace OAI

noncomputable section
open Filter
open scoped ENNReal Topology CStarAlgebra

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in

theorem vectorTrace_real_nonneg_of_nonneg (ξ : H)
    {T : H →L[ℂ] H} (hT : 0 ≤ T) : 0 ≤ (vectorTrace ξ T).re :=
  (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).re_inner_nonneg_right ξ

omit [CompleteSpace H] in

theorem vectorTrace_real_mono (ξ : H)
    {A B : H →L[ℂ] H} (hAB : A ≤ B) :
    (vectorTrace ξ A).re ≤ (vectorTrace ξ B).re := by
  have h := (ContinuousLinearMap.le_def.mp hAB).re_inner_nonneg_right ξ
  change 0 ≤ (vectorTrace ξ (B - A)).re at h
  simpa only [vectorTrace, sub_apply, inner_sub_right,
    Complex.sub_re, sub_nonneg] using h

theorem vectorFugledeKadisonDeterminant_le_norm (ξ : H) (hξ : ‖ξ‖ = 1)
    (T : H →L[ℂ] H) :
    vectorFugledeKadisonDeterminant ξ T ≤ ENNReal.ofReal ‖T‖ := by
  rw [← iInf_sqrt_sq_add_pos ‖T‖ (norm_nonneg T)]
  apply le_iInf
  intro ε
  refine (iInf_le _ ε).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [← exp_half_log_eq_sqrt (by nlinarith [ε.property, sq_nonneg ‖T‖])]
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have h := vectorTrace_real_mono ξ (regularizedLog_le_norm T ε.val ε.property)
  simpa only [vectorTrace_real_scalar ξ hξ, Complex.ofReal_re] using h

theorem regularizedVectorDeterminant_monotone (ξ : H) (T : H →L[ℂ] H) :
    Monotone (fun ε : {r : ℝ // 0 < r} => ENNReal.ofReal
      (Real.exp ((vectorTrace ξ (CFC.log (star T * T + ε.val • (1 : H →L[ℂ] H)))).re / 2))) := by
  intro ε δ hεδ
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply vectorTrace_real_mono ξ
  apply CFC.log_le_log
  · exact add_le_add le_rfl (smul_le_smul_of_nonneg_right hεδ zero_le_one)
  · apply (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos
      (R := ℝ) _ (by simp [IsSelfAdjoint])).mpr
    exact regularizedNormSquare_spectrum_pos T ε.val ε.property

theorem tendsto_regularizedVectorDeterminant
    (ξ : H) (T : H →L[ℂ] H) {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i => ENNReal.ofReal
      (Real.exp ((vectorTrace ξ (CFC.log (star T * T + ε i • (1 : H →L[ℂ] H)))).re / 2)))
      l (𝓝 (vectorFugledeKadisonDeterminant ξ T)) := by
  unfold vectorFugledeKadisonDeterminant
  exact tendsto_monotone_positive_iInf _ (regularizedVectorDeterminant_monotone ξ T) ε hε hlim

end Invariant233

end

end OAI
