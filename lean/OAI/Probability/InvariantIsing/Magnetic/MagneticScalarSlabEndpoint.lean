import OAI.Probability.InvariantIsing.Magnetic.MagneticSlabEndpoint
import OAI.Probability.InvariantIsing.Magnetic.MagneticSlabContinuation
import OAI.Probability.InvariantIsing.Magnetic.MagneticSlabCoefficient
import OAI.Probability.InvariantIsing.Magnetic.MagneticSlabZero

namespace OAI

/-! Uniform endpoint decay of the actual finite-tail square continuation.
The variance may vary arbitrarily as the prescribed spin tends to ±1. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSlabJet_value_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v z : ℝ) :
    |(magneticScalarSlabJet L hL ζ v).value z| ≤ 1 := by
  have htan : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hP := fieldScalarMean_regular L hL measurable_logCosh logCosh_linearGrowth
    htan field_abs_tanh_le_one
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  exact fieldSpinTransition_bound ζ (Real.toNNReal v) hF.1 hF.2 hP.2 z

lemma magneticScalarSlabJet_curvature_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ1 : ζ ≤ 1) (v z : ℝ) :
    (magneticScalarSlabJet L hL ζ v).first z ≤
      1 - ((magneticScalarSlabJet L hL ζ v).value z) ^ 2 := by
  let P := magneticLogCoshMeanJet L hL
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  obtain ⟨K, _, bK⟩ := P.bValue
  obtain ⟨C, _, bC⟩ := P.bFirst
  have hb (y : ℝ) : P.first y + (P.value y) ^ 2 ≤ 1 := by
    have hh := fieldScalarLogCoshSecond_le_spin_variance L hL hL1 y
    change P.first y ≤ 1 - (P.value y) ^ 2 at hh
    linarith
  have hh := fieldCurvatureTransform_le_spin_variance hζ1 (Real.toNNReal v)
    hF.1 hF.2 P.mValue P.mFirst bK bC hb z
  simpa only [magneticScalarSlabJet, MagneticContinuationJet.transition,
    fieldCurvatureTransform, fieldTiltSpatial, pow_two] using hh

lemma magneticScalarSlabJet_third_ratio_bound_pos (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 < ζ) (v z : ℝ) :
    |(magneticScalarSlabJet L hL ζ v).second z /
      (magneticScalarSlabJet L hL ζ v).first z| ≤
      magneticThirdRatioCap ((ζ, 0) :: L) := by
  let K := (ζ, Real.toNNReal v) :: L
  have hK : ∀ av ∈ K, 0 < av.1 := by
    intro av hav
    rcases List.mem_cons.mp hav with h | h
    · simpa only [h] using hζ
    · exact hL av h
  have hr := fieldScalarLogCoshThird_relative K hK z
  have he := magneticScalarSlabJet_eq_cons L hL hζ v
  have hp := magneticScalarSlabJet_curvature_pos L hL hζ.le v z
  rw [abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  rw [he]
  simpa only [K, magneticThirdRatioCap, magneticLogCoshMeanJet] using hr

lemma magneticScalarSlabJet_third_ratio_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v z : ℝ) :
    |(magneticScalarSlabJet L hL ζ v).second z /
      (magneticScalarSlabJet L hL ζ v).first z| ≤
      magneticThirdRatioCap ((ζ, 0) :: L) := by
  rcases eq_or_lt_of_le hζ with he | hp
  · subst ζ
    have hq := magneticScalarSlabJet_curvature_pos L hL (le_refl (0 : ℝ)) v z
    rw [abs_div, abs_of_pos hq]
    apply (div_le_iff₀ hq).mpr
    simpa only [magneticThirdRatioCap, abs_zero, mul_zero, add_zero] using
      magneticScalarSlabJet_zero_third_relative L hL v z
  · exact magneticScalarSlabJet_third_ratio_bound_pos L hL hp v z

def magneticScalarSlabWeighted (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ v s : ℝ) : ℝ :=
  let J := magneticScalarSlabJet L hL ζ v
  let K := magneticScalarSlabContinuationJet L hL A ζ v
  let z := magneticScalarSlabBias L ζ v s
  K.second z - K.first z * (J.second z / J.first z)

lemma magneticScalarSlabContinuation_sandwich (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    (ζ v z : ℝ) :
    ((magneticScalarSlabJet L hL ζ v).value z) ^ 2 ≤
        (magneticScalarSlabContinuationJet L hL A ζ v).value z ∧
      (magneticScalarSlabContinuationJet L hL A ζ v).value z ≤ 1 := by
  let P := magneticLogCoshMeanJet L hL
  let F := fieldScalarValue L (fun y => Real.log (Real.cosh y))
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  obtain ⟨C, _, bC⟩ := P.bValue
  have bP2 (y : ℝ) : |(P.value y) ^ 2| ≤ C ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (bC y) 2
  have bA (y : ℝ) : |A.value y| ≤ 1 := by
    rw [abs_of_nonneg ((sq_nonneg _).trans (hA y).1)]
    exact (hA y).2
  have hsq := fieldSpinTransition_square_le ζ (Real.toNNReal v) hF.1 hF.2 P.mValue bC z
  have hle := fieldSpinTransition_mono_test ζ (Real.toNNReal v) F
    (P.mValue.pow_const 2) A.mValue bP2 bA (fun y => (hA y).1) z
  exact ⟨hsq.trans hle, (le_abs_self _).trans
    (fieldSpinTransition_bound ζ (Real.toNNReal v) hF.1 hF.2 bA z)⟩

theorem magneticScalarSlabWeighted_tendsto_endpoint {ι : Type*} {l : Filter ι}
    (L : List (ℝ × ℝ≥0)) (hL : ∀ av ∈ L, 0 < av.1)
    (hL1 : ∀ av ∈ L, av.1 ≤ 1) (A : MagneticContinuationJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    {ζ c : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hc : c = -1 ∨ c = 1)
    (v s : ι → ℝ) (hs : ∀ᶠ i in l, |s i| < 1) (hslim : Tendsto s l (𝓝 c)) :
    Tendsto (fun i => magneticScalarSlabWeighted L hL A ζ (v i) (s i)) l (𝓝 0) := by
  let P := magneticLogCoshMeanJet L hL
  let F := fieldScalarValue L (fun y => Real.log (Real.cosh y))
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  let J := fun i => magneticScalarSlabJet L hL ζ (v i)
  let K := fun i => magneticScalarSlabContinuationJet L hL A ζ (v i)
  let x := fun i => magneticScalarSlabBias L ζ (v i) (s i)
  have hroot : Tendsto (fun i => (J i).value (x i)) l (𝓝 c) := by
    apply hslim.congr'
    filter_upwards [hs] with i hi
    exact (magneticScalarSlabMean_bias L hL hζ hi (v i)).symm
  have hshift (h : ℝ) : Tendsto (fun i => (J i).value (x i + h)) l (𝓝 c) := by
    rcases hc with rfl | rfl
    · exact magnetic_mean_shift_tendsto_neg_one (fun i => (J i).dValue)
        (fun i => magneticScalarSlabJet_value_bound L hL ζ (v i))
        (fun i z => (magneticScalarSlabJet_curvature_pos L hL hζ (v i) z).le)
        (fun i => magneticScalarSlabJet_curvature_bound L hL hL1 hζ1 (v i)) hroot h
    · exact magnetic_mean_shift_tendsto_one (fun i => (J i).dValue)
        (fun i => magneticScalarSlabJet_value_bound L hL ζ (v i))
        (fun i z => (magneticScalarSlabJet_curvature_pos L hL hζ (v i) z).le)
        (fun i => magneticScalarSlabJet_curvature_bound L hL hL1 hζ1 (v i)) hroot h
  obtain ⟨C, hC, bC⟩ := A.transition_second_uniform P ζ F hF.1 hF.2
    (hasDerivAt_fieldScalarLogCosh L hL)
  obtain ⟨D, hD, bD⟩ := A.transition_third_uniform P ζ F hF.1 hF.2
    (hasDerivAt_fieldScalarLogCosh L hL)
  have hc2 : c ^ 2 = 1 := by rcases hc with rfl | rfl <;> norm_num
  have hends := magnetic_family_continuation_endpoint hc2 hC hD
    (fun i => magneticScalarSlabContinuation_sandwich L hL A hA ζ (v i))
    (fun i => (K i).dValue) (fun i => (K i).dFirst) (fun i => (K i).dSecond)
    (fun i => bC (Real.toNNReal (v i))) (fun i => bD (Real.toNNReal (v i))) hshift
  exact magnetic_family_weighted_endpoint hends.1 hends.2
    (fun i => magneticScalarSlabJet_third_ratio_bound L hL hζ (v i) (x i))

end InvariantIsing

end

end OAI
