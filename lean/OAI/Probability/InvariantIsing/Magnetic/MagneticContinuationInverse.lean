import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationEndpoint

namespace OAI

/-! Ordinary continuation derivatives pulled back through the actual
optimizing bias. The weighted second derivative has zero boundary limits. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

def magneticContinuationPullback (h : FieldStep) (J : MagneticContinuationJet) (s : ℝ) : ℝ :=
  J.value (magneticBias h s)

def magneticContinuationPullbackFirst (h : FieldStep) (J : MagneticContinuationJet) (s : ℝ) : ℝ :=
  J.first (magneticBias h s) / fieldBiasCurvature h (magneticBias h s)

def magneticContinuationPullbackSecond (h : FieldStep) (J : MagneticContinuationJet) (s : ℝ) : ℝ :=
  J.second (magneticBias h s) / (fieldBiasCurvature h (magneticBias h s)) ^ 2 -
    J.first (magneticBias h s) * fieldBiasThird h (magneticBias h s) /
      (fieldBiasCurvature h (magneticBias h s)) ^ 3

lemma magneticContinuationPullback_hasDerivAt (h : FieldStep) (J : MagneticContinuationJet)
    {s : ℝ} (hs : |s| < 1) :
    HasDerivAt (magneticContinuationPullback h J)
      (magneticContinuationPullbackFirst h J s) s := by
  convert (J.dValue (magneticBias h s)).comp s (hasDerivAt_magneticBias h hs) using 1
  · rfl
  · simp only [magneticContinuationPullbackFirst, div_eq_mul_inv]

lemma magneticContinuationPullbackFirst_hasDerivAt (h : FieldStep) (J : MagneticContinuationJet)
    {s : ℝ} (hs : |s| < 1) :
    HasDerivAt (magneticContinuationPullbackFirst h J)
      (magneticContinuationPullbackSecond h J s) s := by
  have hZ : HasDerivAt (magneticBias h) (1 / fieldBiasCurvature h (magneticBias h s)) s := by
    simpa only [one_div] using hasDerivAt_magneticBias h hs
  exact inverse_mean_pullback_quotient (fieldBiasCurvature_pos h (magneticBias h s)).ne'
    hZ rfl rfl (J.dFirst (magneticBias h s)) (hasDerivAt_fieldBiasCurvature h (magneticBias h s))

lemma magneticContinuationPullback_second_deriv (h : FieldStep) (J : MagneticContinuationJet)
    {s : ℝ} (hs : |s| < 1) :
    deriv (deriv (magneticContinuationPullback h J)) s =
      magneticContinuationPullbackSecond h J s := by
  have hh := magneticContinuationPullbackFirst_hasDerivAt h J hs
  apply HasDerivAt.deriv
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2] with t ht
  exact (magneticContinuationPullback_hasDerivAt h J (abs_lt.mpr ht)).deriv

lemma magneticContinuation_weighted_second (h : FieldStep) (J : MagneticContinuationJet) (s : ℝ) :
    (magneticCurvature h s) ^ 2 * magneticContinuationPullbackSecond h J s =
      J.second (magneticBias h s) - J.first (magneticBias h s) *
        (fieldBiasThird h (magneticBias h s) / fieldBiasCurvature h (magneticBias h s)) := by
  unfold magneticCurvature magneticContinuationPullbackSecond
  field_simp [(fieldBiasCurvature_pos h (magneticBias h s)).ne']

lemma magneticFieldLevel_weighted_second_endpoint (h : FieldStep) (i : Fin (h.depth + 1)) :
    Tendsto (fun s => (magneticCurvature h s) ^ 2 *
      deriv (deriv (fun t => magneticFieldLevel h t i)) s)
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  obtain ⟨J, hJ⟩ := magneticLevelAtBias_has_bounded_jet h i
  have hvalue : magneticContinuationPullback h J = fun t => magneticFieldLevel h t i := by
    funext t
    change J.value (magneticBias h t) = magneticLevelAtBias h (magneticBias h t) i
    exact congrFun hJ (magneticBias h t)
  apply (magneticContinuation_weighted_endpoint h i J hJ).congr'
  have hN : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), -1 < s :=
    (show ∀ᶠ s : ℝ in 𝓝 (1 : ℝ), -1 < s from Ioi_mem_nhds (by norm_num)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hN, self_mem_nhdsWithin] with s hs hs1
  rw [← hvalue, magneticContinuationPullback_second_deriv h J (abs_lt.mpr ⟨hs, hs1⟩)]
  exact (magneticContinuation_weighted_second h J s).symm

lemma magneticFieldLevel_weighted_second_neg_endpoint (h : FieldStep) (i : Fin (h.depth + 1)) :
    Tendsto (fun s => (magneticCurvature h s) ^ 2 *
      deriv (deriv (fun t => magneticFieldLevel h t i)) s)
      (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
  obtain ⟨J, hJ⟩ := magneticLevelAtBias_has_bounded_jet h i
  have hvalue : magneticContinuationPullback h J = fun t => magneticFieldLevel h t i := by
    funext t
    change J.value (magneticBias h t) = magneticLevelAtBias h (magneticBias h t) i
    exact congrFun hJ (magneticBias h t)
  apply (magneticContinuation_weighted_neg_endpoint h i J hJ).congr'
  have hN : ∀ᶠ s : ℝ in 𝓝[>] (-1 : ℝ), s < 1 :=
    (show ∀ᶠ s : ℝ in 𝓝 (-1 : ℝ), s < 1 from Iio_mem_nhds (by norm_num)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hN, self_mem_nhdsWithin] with s hs hs1
  rw [← hvalue, magneticContinuationPullback_second_deriv h J (abs_lt.mpr ⟨hs1, hs⟩)]
  exact (magneticContinuation_weighted_second h J s).symm

end InvariantIsing

end

end OAI
