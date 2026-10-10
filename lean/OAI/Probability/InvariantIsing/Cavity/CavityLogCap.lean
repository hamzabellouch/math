import OAI.Probability.InvariantIsing.Cavity.CavityCappedLog

namespace OAI

/-! Removing the upper cap after the quadratic cascade transformation.
The error is bounded by a second energy moment under the full tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Topology

namespace InvariantIsing

lemma cavity_log_cap_error {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) ν) (T : ℝ)
    (hg : Integrable (fun x => max (H x - T) 0) (ν.tilted H)) :
    0 ≤ Real.log (∫ x, Real.exp (H x) ∂ν) -
        Real.log (∫ x, Real.exp (min (H x) T) ∂ν) ∧
      Real.log (∫ x, Real.exp (H x) ∂ν) -
        Real.log (∫ x, Real.exp (min (H x) T) ∂ν) ≤
          ∫ x, max (H x - T) 0 ∂ν.tilted H := by
  let := isProbabilityMeasure_tilted he
  let g := fun x => max (H x - T) 0
  have hge : Measurable g := (hH.sub_const T).max measurable_const
  have hc : Integrable (fun x => Real.exp (min (H x) T)) ν := by
    apply Integrable.of_bound ((hH.min measurable_const).exp).aestronglyMeasurable (Real.exp T)
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (min_le_right _ _)
  have hpos := integral_exp_pos he
  have hcpos := integral_exp_pos hc
  have hsmall : (∫ x, Real.exp (min (H x) T) ∂ν) ≤ ∫ x, Real.exp (H x) ∂ν :=
    integral_mono hc he (fun x => Real.exp_le_exp.mpr (min_le_left _ _))
  refine ⟨sub_nonneg.mpr (Real.log_le_log hcpos hsmall), ?_⟩
  have hneg : Integrable (fun x => Real.exp (-g x)) (ν.tilted H) := by
    apply Integrable.of_bound hge.neg.exp.aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (Real.exp_le_exp.mpr (neg_nonpos.mpr (le_max_right _ _))).trans_eq Real.exp_zero
  have hsum : (H + fun x => -g x) = fun x => min (H x) T := by
    funext x
    change H x + -max (H x - T) 0 = min (H x) T
    by_cases h : H x ≤ T
    · rw [max_eq_right (sub_nonpos.mpr h), min_eq_left h]
      ring
    · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge h)), min_eq_right (le_of_not_ge h)]
      ring
  have hid : (∫ x, Real.exp (-g x) ∂ν.tilted H) =
      (∫ x, Real.exp (min (H x) T) ∂ν) / ∫ x, Real.exp (H x) ∂ν := by
    rw [integral_exp_tilted, hsum]
  have hj := exp_integral_le_partition hg.neg hneg
  have hl := (Real.le_log_iff_exp_le (integral_exp_pos hneg)).mpr hj
  simp only [Pi.neg_apply] at hl
  rw [integral_neg, hid, Real.log_div hcpos.ne' hpos.ne'] at hl
  linarith

lemma cavity_log_cap_error_of_second_moment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) ν) {T : ℝ} (hT : 0 < T)
    (hi : Integrable (fun x => H x ^ 2) (ν.tilted H)) :
    0 ≤ Real.log (∫ x, Real.exp (H x) ∂ν) -
        Real.log (∫ x, Real.exp (min (H x) T) ∂ν) ∧
      Real.log (∫ x, Real.exp (H x) ∂ν) -
        Real.log (∫ x, Real.exp (min (H x) T) ∂ν) ≤
          (∫ x, H x ^ 2 ∂ν.tilted H) / T := by
  have hb x : max (H x - T) 0 ≤ H x ^ 2 / T := by
    apply max_le
    · apply (le_div_iff₀ hT).mpr
      nlinarith [sq_nonneg (H x - T)]
    · exact div_nonneg (sq_nonneg _) hT.le
  have hig : Integrable (fun x => max (H x - T) 0) (ν.tilted H) := by
    apply (hi.div_const T).mono' ((hH.sub_const T).max measurable_const).aestronglyMeasurable
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact hb x)
  have hh := cavity_log_cap_error ν H hH he T hig
  refine ⟨hh.1, hh.2.trans ?_⟩
  simpa only [integral_div] using integral_mono hig (hi.div_const T) hb

theorem cavity_log_cap_mean_error {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω, x))) (ν ω))
    (hi : ∀ᵐ ω ∂P, Integrable (fun x => H (ω, x)^2) ((ν ω).tilted (fun x => H (ω, x))))
    (hmi : Integrable (fun ω => ∫ x, H (ω, x)^2 ∂(ν ω).tilted (fun x => H (ω, x))) P)
    {K T : ℝ} (hK : (∫ ω, ∫ x, H (ω, x)^2 ∂(ν ω).tilted (fun x => H (ω, x)) ∂P) ≤ K)
    (hT : 0 < T) :
    0 ≤ (∫ ω, Real.log (∫ x, Real.exp (H (ω, x)) ∂ν ω) -
      Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω) ∂P) ∧
    (∫ ω, Real.log (∫ x, Real.exp (H (ω, x)) ∂ν ω) -
      Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω) ∂P) ≤ K / T := by
  let D := fun ω => Real.log (∫ x, Real.exp (H (ω, x)) ∂ν ω) -
    Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)
  let J := fun ω => ∫ x, H (ω, x)^2 ∂(ν ω).tilted (fun x => H (ω, x))
  have hb : ∀ᵐ ω ∂P, 0 ≤ D ω ∧ D ω ≤ J ω / T := by
    filter_upwards [he, hi] with ω hωe hωi
    exact cavity_log_cap_error_of_second_moment (ν ω) (fun x => H (ω, x))
      (hH.comp measurable_prodMk_left) hωe hT hωi
  have hm : Measurable D :=
    (measurable_cavityWeightNormalizer ν hν (fun p => Real.exp (H p)) hH.exp).log.sub
      (measurable_cavityWeightNormalizer ν hν (fun p => Real.exp (min (H p) T))
        (hH.min measurable_const).exp).log
  have hdi : Integrable D P := (hmi.div_const T).mono' hm.aestronglyMeasurable (by
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
    exact hω.2)
  refine ⟨integral_nonneg_of_ae (hb.mono (fun _ h => h.1)), ?_⟩
  calc
    _ ≤ ∫ ω, J ω / T ∂P := integral_mono_ae hdi (hmi.div_const T) (hb.mono fun _ h => h.2)
    _ = (∫ ω, J ω ∂P) / T := integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right hK hT.le

end InvariantIsing

end

end OAI
