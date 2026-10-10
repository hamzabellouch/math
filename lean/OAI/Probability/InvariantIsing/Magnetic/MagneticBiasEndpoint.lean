import OAI.Probability.InvariantIsing.Magnetic.MagneticDerivativeLimit
import OAI.Probability.InvariantIsing.Magnetic.MagneticRelativeThird

namespace OAI

/-! Endpoint behavior of the actual inverse bias and the weighted
continuation curvature. No asymptotic expansion of the field is used. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma fieldBiasMean_strict_bounds (h : FieldStep) (b : ℝ) :
    -1 < fieldBiasMean h b ∧ fieldBiasMean h b < 1 := by
  have hp := strictMono_fieldBiasMean h (show b < b + 1 by linarith)
  have hm := strictMono_fieldBiasMean h (show b - 1 < b by linarith)
  have hbp := (abs_le.mp ((fieldBiasMean_regular h).2 (b + 1))).2
  have hbm := (abs_le.mp ((fieldBiasMean_regular h).2 (b - 1))).1
  exact ⟨by linarith, by linarith⟩

lemma magneticBias_tendsto_one (h : FieldStep) :
    Tendsto (magneticBias h) (𝓝[<] (1 : ℝ)) atTop := by
  apply tendsto_atTop.2
  intro b
  have hN : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), -1 < s ∧ fieldBiasMean h b < s := by
    have h1 : ∀ᶠ s : ℝ in 𝓝 (1 : ℝ), -1 < s :=
      Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 1)
    have h2 : ∀ᶠ s : ℝ in 𝓝 (1 : ℝ), fieldBiasMean h b < s :=
      Ioi_mem_nhds (fieldBiasMean_strict_bounds h b).2
    exact (h1.and h2).filter_mono nhdsWithin_le_nhds
  filter_upwards [hN, self_mem_nhdsWithin] with s hs hs1
  apply le_of_lt
  apply (strictMono_fieldBiasMean h).lt_iff_lt.mp
  rw [fieldBiasMean_magneticBias h (abs_lt.mpr ⟨hs.1, hs1⟩)]
  exact hs.2

lemma magneticBias_tendsto_neg_one (h : FieldStep) :
    Tendsto (magneticBias h) (𝓝[>] (-1 : ℝ)) atBot := by
  apply tendsto_atBot.2
  intro b
  have hN : ∀ᶠ s : ℝ in 𝓝[>] (-1 : ℝ), s < 1 ∧ s < fieldBiasMean h b := by
    have h1 : ∀ᶠ s : ℝ in 𝓝 (-1 : ℝ), s < 1 :=
      Iio_mem_nhds (by norm_num : (-1 : ℝ) < 1)
    have h2 : ∀ᶠ s : ℝ in 𝓝 (-1 : ℝ), s < fieldBiasMean h b :=
      Iio_mem_nhds (fieldBiasMean_strict_bounds h b).1
    exact (h1.and h2).filter_mono nhdsWithin_le_nhds
  filter_upwards [hN, self_mem_nhdsWithin] with s hs hs1
  apply le_of_lt
  apply (strictMono_fieldBiasMean h).lt_iff_lt.mp
  rw [fieldBiasMean_magneticBias h (abs_lt.mpr ⟨hs1, hs.1⟩)]
  exact hs.2

lemma fieldBiasThird_quotient_bound (h : FieldStep) (b : ℝ) :
    |fieldBiasThird h b / fieldBiasCurvature h b| ≤
      magneticThirdRatioCap (scalarFieldIncrements h) := by
  rw [abs_div, abs_of_pos (fieldBiasCurvature_pos h b)]
  exact (div_le_iff₀ (fieldBiasCurvature_pos h b)).mpr (fieldBiasThird_relative h b)

lemma magnetic_weighted_continuation_limit (h : FieldStep)
    {F G D E : ℝ → ℝ} {c L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hF : ∀ x, HasDerivAt F (G x) x) (hG : ∀ x, HasDerivAt G (D x) x)
    (hD : ∀ x, HasDerivAt D (E x) x) (bD : ∀ x, |D x| ≤ L)
    (bE : ∀ x, |E x| ≤ K) (hlim : Tendsto F atTop (𝓝 c)) :
    Tendsto (fun x => D x - G x * (fieldBiasThird h x / fieldBiasCurvature h x))
      atTop (𝓝 0) := by
  have hg := magnetic_derivative_tendsto_zero hL hF hG bD hlim
  have hd := magnetic_derivative_tendsto_zero hK hG hD bE hg
  have hp : Tendsto (fun x => G x * (fieldBiasThird h x / fieldBiasCurvature h x))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun x => ?_)
      (show Tendsto (fun x => |G x| * magneticThirdRatioCap (scalarFieldIncrements h)) atTop (𝓝 0) by
        simpa only [Real.norm_eq_abs, abs_zero, zero_mul] using
          hg.norm.mul_const (magneticThirdRatioCap (scalarFieldIncrements h)))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (fieldBiasThird_quotient_bound h x) (abs_nonneg _)
  simpa only [sub_zero] using hd.sub hp

end InvariantIsing

end

end OAI
