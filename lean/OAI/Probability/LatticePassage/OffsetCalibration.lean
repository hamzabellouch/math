import OAI.Probability.LatticePassage.CalibrationShift
import OAI.Probability.LatticePassage.MetricConcentration

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Finset

lemma mean_passageTime_endpoint_lipschitz (s t : Vertex) :
    |(∫ ω, passageTime ω 0 s ∂environmentLaw) -
      (∫ ω, passageTime ω 0 t ∂environmentLaw)| ≤ (latticeDistance s t : ℝ) := by
  have he : (∫ ω, passageTime ω 0 s ∂environmentLaw) -
      (∫ ω, passageTime ω 0 t ∂environmentLaw) =
      ∫ ω, targetCocycle 0 ω s t ∂environmentLaw := by
    rw [← integral_sub (integrable_passageTime 0 s) (integrable_passageTime 0 t)]
    apply integral_congr_ae
    filter_upwards [passageTime_properties] with ω hω
    unfold targetCocycle
    rw [hω.2.2.1 s 0, hω.2.2.1 t 0]
  rw [he]
  have hnorm := norm_integral_le_integral_norm (μ := environmentLaw) (fun ω => targetCocycle 0 ω s t)
  simp only [Real.norm_eq_abs] at hnorm
  apply hnorm.trans
  apply (integral_mono_ae (integrable_targetCocycle 0 s t).abs (integrable_passageTime s t)
    (by filter_upwards [targetCocycle_dominated] with ω hω; exact hω 0 s t)).trans
  exact mean_passageTime_le_distance s t

noncomputable def offsetTargetCocycle (s d : Vertex) (N : ℕ)
    (ω : Environment) (x y : Vertex) : ℝ :=
  (∑ k ∈ range N, targetCocycle (s+scaleVertex (k+1) d) ω x y) / N

@[fun_prop] lemma measurable_offsetTargetCocycle (s d x y : Vertex) (N : ℕ) :
    Measurable (fun ω => offsetTargetCocycle s d N ω x y) := by
  unfold offsetTargetCocycle
  fun_prop

lemma integrable_offsetTargetCocycle (s d x y : Vertex) (N : ℕ) :
    Integrable (fun ω => offsetTargetCocycle s d N ω x y) environmentLaw :=
  (integrable_finsetSum _ (fun _k _ => integrable_targetCocycle _ _ _)).div_const _

lemma integral_offset_target_step (s d : Vertex) (k : ℕ) :
    (∫ ω, targetCocycle (s+scaleVertex (k+1) d) ω 0 d ∂environmentLaw) =
      (∫ ω, passageTime ω 0 (s+scaleVertex (k+1) d) ∂environmentLaw) -
      (∫ ω, passageTime ω 0 (s+scaleVertex k d) ∂environmentLaw) := by
  unfold targetCocycle
  rw [integral_sub (integrable_passageTime _ _) (integrable_passageTime _ _)]
  have he : s+scaleVertex (k+1) d = d+(s+scaleVertex k d) := by
    rw [scaleVertex_succ]
    abel
  have ht := mean_passageTime_translation d 0 (s+scaleVertex k d)
  simp only [add_zero] at ht
  rw [he, ht]

theorem integral_offsetTargetCocycle (s d : Vertex) (N : ℕ) :
    (∫ ω, offsetTargetCocycle s d N ω 0 d ∂environmentLaw) =
      ((∫ ω, passageTime ω 0 (s+scaleVertex N d) ∂environmentLaw) -
        (∫ ω, passageTime ω 0 s ∂environmentLaw)) / N := by
  unfold offsetTargetCocycle
  rw [integral_div, integral_finsetSum _ (fun _k _ => integrable_targetCocycle _ _ _)]
  simp_rw [integral_offset_target_step]
  rw [sum_range_sub (fun k => ∫ ω, passageTime ω 0 (s+scaleVertex k d) ∂environmentLaw)]
  have hz : scaleVertex 0 d = (0 : Vertex) := by ext <;> simp [scaleVertex]
  rw [hz, add_zero]

theorem offsetTargetCocycle_mean_error (s d : Vertex) (N : ℕ) :
    |(∫ ω, offsetTargetCocycle s d N ω 0 d ∂environmentLaw) -
      meanPassageSequence d N/N| ≤ 2*(latticeDistance 0 s : ℝ)/N := by
  rw [integral_offsetTargetCocycle, ← sub_div, abs_div,
    show |(N : ℝ)| = (N : ℝ) from abs_of_nonneg (Nat.cast_nonneg N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have h₁ := mean_passageTime_endpoint_lipschitz (s+scaleVertex N d) (scaleVertex N d)
  have hdist : latticeDistance (s+scaleVertex N d) (scaleVertex N d) = latticeDistance 0 s := by
    simp [latticeDistance]
  rw [hdist] at h₁
  have h₂ := mean_passageTime_le_distance 0 s
  have h₃ := mean_passageTime_nonneg 0 s
  have htri := abs_sub ((∫ ω, passageTime ω 0 (s+scaleVertex N d) ∂environmentLaw) -
    meanPassageSequence d N) (∫ ω, passageTime ω 0 s ∂environmentLaw)
  rw [abs_of_nonneg h₃] at htri
  change |(∫ ω, passageTime ω 0 (s+scaleVertex N d) ∂environmentLaw) -
    meanPassageSequence d N| ≤ _ at h₁
  have he : (∫ ω, passageTime ω 0 (s+scaleVertex N d) ∂environmentLaw) -
      (∫ ω, passageTime ω 0 s ∂environmentLaw) - meanPassageSequence d N =
      ((∫ ω, passageTime ω 0 (s+scaleVertex N d) ∂environmentLaw) - meanPassageSequence d N) -
      (∫ ω, passageTime ω 0 s ∂environmentLaw) := by ring
  rw [he]
  linarith

end CompanionFPP

end OAI
