import Mathlib
import OAI.Probability.Ballisticity.Estimates.ScaledMaxMoment
import OAI.Probability.Ballisticity.Estimates.MaxTailDecomposition

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma cappedTailMoment_scaled_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : ∀ x, 0 ≤ X x)
    {z A L : ℝ} (hz : 0 < z) (hL : 0 ≤ L) :
    cappedTailMoment μ (fun x => X x/z) A L =
      (∫ x, (if A*z < X x then min ((X x)^2) ((L*z)^2) else 0) ∂μ)/z^2 := by
  unfold cappedTailMoment
  rw [← integral_div]
  congr 1
  funext x
  simp only [lt_div_iff₀ hz]
  split_ifs
  · nth_rw 1 [show L = (L*z)/z from (mul_div_cancel_right₀ L (ne_of_gt hz)).symm]
    rw [min_div_div_right hz.le,div_pow,sq_min_nonneg (hX x) (mul_nonneg hL hz.le)]
  · simp

lemma iid_scaled_max_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hne : 0 < μ {ω | X 0 ω ≠ 0}) {z A L : ℝ} (hz : 0 < z) (hA : 0 < A) (hL : 1 ≤ L)
    (n : ℕ) (hn : (n:ℝ) ≤ fluctuationScale μ (X 0) z) :
    cappedTailMoment μ (fun ω => partialSumMax (fun k => X k ω) n/z) A L ≤
      2048/A^2+16*((truncatedVariance μ (X 0) (L*z)-truncatedVariance μ (X 0) z)/
        truncatedVariance μ (X 0) z)+16*fluctuationScale μ (X 0) z*μ.real {ω | z < |X 0 ω|} := by
  let m := truncatedVariance μ (X 0) z
  let D := truncatedVariance μ (X 0) (L*z)-m
  let p := μ.real {ω | z < |X 0 ω|}
  have hm : 0 < m := truncatedVariance_pos μ (X 0) (hX 0) hne hz
  have hD : 0 ≤ D := sub_nonneg.mpr (truncatedVariance_mono μ (X 0) (hX 0) hz.le (by nlinarith))
  have hp : 0 ≤ p := measureReal_nonneg
  have hn0 : 0 ≤ (n:ℝ) := by positivity
  have hnM : (n:ℝ)*m ≤ z^2 := (le_div_iff₀ hm).mp hn
  have hnSq : (n:ℝ)^2*m^2 ≤ z^4 := by
    have hh := pow_le_pow_left₀ (mul_nonneg hn0 hm.le) hnM 2
    nlinarith [hh]
  have hfour : 32*(n:ℝ)*z^2*m+96*(n:ℝ)^2*m^2 ≤ 128*z^4 := by
    nlinarith [mul_le_mul_of_nonneg_left hnM (sq_nonneg z)]
  have hz2 := sq_pos_of_pos hz
  have hA2 := sq_pos_of_pos hA
  have hAz2 := sq_pos_of_pos (mul_pos hA hz)
  have hfirst : ((16/(A*z)^2)*(32*(n:ℝ)*z^2*m+96*(n:ℝ)^2*m^2))/z^2 ≤ 2048/A^2 := by
    calc
      _ ≤ ((16/(A*z)^2)*(128*z^4))/z^2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfour (by positivity)) hz2.le
      _ = _ := by field_simp; ring
  have hsecond : (16*(n:ℝ)*(D+z^2*p))/z^2 ≤ 16*(D/m)+16*(z^2/m)*p := by
    rw [div_le_iff₀ hz2]
    have hh := mul_le_mul_of_nonneg_right hnM (add_nonneg hD (mul_nonneg hz2.le hp))
    apply (mul_le_mul_iff_of_pos_right hm).mp
    field_simp
    nlinarith [hh]
  rw [cappedTailMoment_scaled_eq μ _ (fun ω => partialSumMax_nonneg _ _) hz (by linarith)]
  apply (div_le_div_of_nonneg_right (integral_iid_max_tail_le μ X hX hind hident hsym
    hz.le (by nlinarith) (mul_pos hA hz) n) hz2.le).trans
  rw [add_div]
  simpa only [add_assoc,fluctuationScale,m,D,p] using add_le_add hfirst hsecond

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma iid_scaled_max_tail_variance_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hne : 0 < μ {ω | X 0 ω ≠ 0}) {z A L : ℝ} (hz : 0 < z) (hA : 0 < A) (hL : 1 ≤ L)
    (n : ℕ) (hn : (n:ℝ) ≤ fluctuationScale μ (X 0) z) :
    cappedTailMoment μ (fun ω => partialSumMax (fun k => X k ω) n/z) A L ≤
      2048/A^2+16*((truncatedVariance μ (X 0) (L*z)-truncatedVariance μ (X 0) z)/
        truncatedVariance μ (X 0) z)+(64/3)*((truncatedVariance μ (X 0) z-truncatedVariance μ (X 0) (z/2))/
        truncatedVariance μ (X 0) z) := by
  have hh := fluctuation_tail_difference μ (X 0) (hX 0) hne hz (show (0:ℝ)<1 by norm_num)
  simp only [one_mul,one_pow,mul_one] at hh
  have hb := iid_scaled_max_tail_le μ X hX hind hident hsym hne hz hA hL n hn
  nlinarith [hh]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma successful_tail_profile_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (z : ℕ → ℝ) (hz : ∀ n, 0 < z n) (hzinf : Tendsto z atTop atTop)
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) {A L R G : ℝ} (hA : 0 < A) (hAL : A < L) (hL : 1 ≤ L)
    (hHt : ∀ᶠ n in atTop, (H n:ℝ) ≤ fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (z n))
    (hR : Tendsto (fun n => truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (L*z n)/
      truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (z n)) atTop (𝓝 R))
    (hG : Tendsto (fun n => truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (z n/2)/
      truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (z n)) atTop (𝓝 G)) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
    limsup (fun n => cappedTailMoment (successfulAverage ν ℓ (H n))
      (fun X => medianDeviation ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) (H n) X/z n) A L) atTop ≤
      (16000/p^2)*(2048/(A/40)^2+16*(R-1)+(64/3)*(1-G)) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
  let μ := independentConditionedPairLaw ν ℓ
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ hp
  let X := commonIncrementProcess ℓ f
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hm (n) : truncatedVariance μ (X 0) (z n) ≠ 0 :=
    ne_of_gt (truncatedVariance_pos μ (X 0) (measurable_commonIncrementProcess ℓ f 0) hne (hz n))
  have hlim : Tendsto (fun n => 2048/(A/40)^2+
      16*((truncatedVariance μ (X 0) (L*z n)-truncatedVariance μ (X 0) (z n))/truncatedVariance μ (X 0) (z n))+
      (64/3)*((truncatedVariance μ (X 0) (z n)-truncatedVariance μ (X 0) (z n/2))/truncatedVariance μ (X 0) (z n)))
      atTop (𝓝 (2048/(A/40)^2+16*(R-1)+(64/3)*(1-G))) := by
    simp only [sub_div,div_self (hm _)]
    exact (tendsto_const_nhds.add (tendsto_const_nhds.mul (hR.sub tendsto_const_nhds))).add
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hG))
  have hbound : limsup (fun n => cappedTailMoment μ (fun P => partialSumMax (fun k => X k P) (H n)/z n) (A/40) L) atTop ≤
      2048/(A/40)^2+16*(R-1)+(64/3)*(1-G) := by
    rw [← hlim.limsup_eq]
    have hev : ∀ᶠ n in atTop, cappedTailMoment μ (fun P => partialSumMax (fun k => X k P) (H n)/z n) (A/40) L ≤
        2048/(A/40)^2+
        16*((truncatedVariance μ (X 0) (L*z n)-truncatedVariance μ (X 0) (z n))/truncatedVariance μ (X 0) (z n))+
        (64/3)*((truncatedVariance μ (X 0) (z n)-truncatedVariance μ (X 0) (z n/2))/truncatedVariance μ (X 0) (z n)) := by
      filter_upwards [hHt] with n hn
      exact iid_scaled_max_tail_variance_le μ X (measurable_commonIncrementProcess ℓ f)
        (commonIncrements_independent ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f)
        (commonIncrements_identDistrib ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f)
        (independent_commonWordIncrement_symmetric ν ℓ htrans f) hne (hz n) (by positivity) hL (H n) hn
    have h0 : ∀ n, (0:ℝ) ≤ cappedTailMoment μ (fun P => partialSumMax (fun k => X k P) (H n)/z n) (A/40) L :=
      fun n => integral_nonneg fun P => by split_ifs <;> positivity
    exact limsup_le_limsup hev (isCoboundedUnder_le_of_le atTop h0) hlim.isBoundedUnder_le
  have hh := (successfulMedian_moment_transfer ν hue e f htrans H hH z hz hzinf hA hAL).2
  exact hh.trans (mul_le_mul_of_nonneg_left hbound (by positivity))

end DirectionalTransience

end

end

end OAI
