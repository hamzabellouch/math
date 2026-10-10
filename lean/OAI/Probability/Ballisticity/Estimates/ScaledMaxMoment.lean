import Mathlib
import OAI.Probability.Ballisticity.Estimates.FullCapTransfer

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma sq_min_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (min a b)^2 = min (a^2) (b^2) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h,min_eq_left (pow_le_pow_left₀ ha h 2)]
  · rw [min_eq_right h,min_eq_right (pow_le_pow_left₀ hb h 2)]

lemma cappedMoment_scaled_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : ∀ x, 0 ≤ X x)
    {r b : ℝ} (hr : 0 < r) (hb : 0 ≤ b) :
    cappedMoment μ (fun x => X x/r) b = truncatedVariance μ X (b*r)/r^2 := by
  unfold cappedMoment truncatedVariance
  rw [← integral_div]
  congr 1
  funext x
  nth_rw 1 [show b = (b*r)/r from (mul_div_cancel_right₀ b (ne_of_gt hr)).symm]
  rw [min_div_div_right hr.le,div_pow,sq_min_nonneg (hX x) (mul_nonneg hb hr.le)]

lemma iid_scaled_max_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {r b : ℝ} (hr : 0 < r) (hb : 0 ≤ b) (n : ℕ) :
    cappedMoment μ (fun ω => partialSumMax (fun k => X k ω) n/r) b ≤
      5*(n:ℝ)*truncatedVariance μ (X 0) (b*r)/r^2 := by
  rw [cappedMoment_scaled_eq μ _ (fun ω => partialSumMax_nonneg _ _) hr hb]
  exact div_le_div_of_nonneg_right
    (integral_partialSumMax_capped_le μ X hX hind hident hsym (mul_nonneg hb hr.le) n) (sq_nonneg r)

lemma scaled_max_moment_ratio_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hne : 0 < μ {ω | X 0 ω ≠ 0})
    {r b t : ℝ} (hr : 0 < r) (hb : 0 ≤ b) (n : ℕ)
    (hn : (n:ℝ) ≤ t*fluctuationScale μ (X 0) r) :
    cappedMoment μ (fun ω => partialSumMax (fun k => X k ω) n/r) b ≤
      5*t*(truncatedVariance μ (X 0) (b*r)/truncatedVariance μ (X 0) r) := by
  have hm : 0 < truncatedVariance μ (X 0) r := truncatedVariance_pos μ (X 0) (hX 0) hne hr
  have hm0 := truncatedVariance_nonneg μ (X 0) (b*r)
  have hmul : (n:ℝ)*truncatedVariance μ (X 0) r ≤ t*r^2 := by
    rw [fluctuationScale,← mul_div_assoc] at hn
    exact (le_div_iff₀ hm).mp hn
  apply (iid_scaled_max_moment_le μ X hX hind hident hsym hr hb n).trans
  rw [div_le_iff₀ (sq_pos_of_pos hr)]
  have heq : (5*t*(truncatedVariance μ (X 0) (b*r)/truncatedVariance μ (X 0) r))*r^2 =
      (5*truncatedVariance μ (X 0) (b*r))*(t*r^2)/truncatedVariance μ (X 0) r := by ring
  rw [heq,le_div_iff₀ hm]
  nlinarith [mul_le_mul_of_nonneg_left hmul (mul_nonneg (by norm_num : (0:ℝ) ≤ 5) hm0)]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma successful_small_variance_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrinf : Tendsto r atTop atTop)
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) {b t F : ℝ} (hb : 0 < b)
    (hHt : ∀ᶠ n in atTop, (H n:ℝ) ≤ t*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r n))
    (hF : Tendsto (fun n => truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (b*r n) /
      truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r n)) atTop (𝓝 F)) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
    limsup (fun n => cappedMoment (successfulAverage ν ℓ (H n))
      (fun X => medianDeviation ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) (H n) X/r n) b) atTop ≤
      (40000/p^2)*t*F := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
  let μ := independentConditionedPairLaw ν ℓ
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ hp
  let X := commonIncrementProcess ℓ f
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hM := successfulMedian_moment_transfer ν hue e f htrans H hH r hr hrinf
    (A := b/2) (L := b) (by positivity) (by linarith)
  have hlim : Tendsto (fun n => 5*t*(truncatedVariance μ (X 0) (b*r n)/truncatedVariance μ (X 0) (r n)))
      atTop (𝓝 (5*t*F)) := tendsto_const_nhds.mul hF
  have hbound : limsup (fun n => cappedMoment μ (fun P => partialSumMax (fun k => X k P) (H n)/r n) b) atTop ≤ 5*t*F := by
    rw [← hlim.limsup_eq]
    have hev : ∀ᶠ n in atTop, cappedMoment μ (fun P => partialSumMax (fun k => X k P) (H n)/r n) b ≤
        5*t*(truncatedVariance μ (X 0) (b*r n)/truncatedVariance μ (X 0) (r n)) := by
      filter_upwards [hHt] with n hn
      exact scaled_max_moment_ratio_bound μ X (measurable_commonIncrementProcess ℓ f)
        (commonIncrements_independent ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f)
        (commonIncrements_identDistrib ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f)
        (independent_commonWordIncrement_symmetric ν ℓ htrans f) hne (hr n) hb.le (H n) hn
    have h0 : ∀ n, (0:ℝ) ≤ cappedMoment μ (fun P => partialSumMax (fun k => X k P) (H n)/r n) b :=
      fun n => integral_nonneg fun P => sq_nonneg _
    exact limsup_le_limsup hev (isCoboundedUnder_le_of_le atTop h0) hlim.isBoundedUnder_le
  have hC : 0 ≤ 8000/p^2 := by positivity
  calc
    _ ≤ (8000/p^2)*limsup (fun n => cappedMoment μ (fun P => partialSumMax (fun k => X k P) (H n)/r n) b) atTop := hM.1
    _ ≤ (8000/p^2)*(5*t*F) := mul_le_mul_of_nonneg_left hbound hC
    _ = _ := by ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience
lemma exists_block_count {T t : ℝ} (hT : 0 < T) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ J : ℕ, T < (J:ℝ)*t ∧ (J:ℝ)*t ≤ 2*T+1 := by
  refine ⟨⌈2*T/t⌉₊,?_,?_⟩
  · have hh := Nat.le_ceil (2*T/t)
    have hh := mul_le_mul_of_nonneg_right hh ht.le
    rw [div_mul_cancel₀ _ ht.ne'] at hh
    linarith
  · have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2*T/t)
    have hh := mul_lt_mul_of_pos_right hh ht
    rw [add_mul,div_mul_cancel₀ _ ht.ne',one_mul] at hh
    linarith

lemma eventually_ceil_horizon_covered (n : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (M : ℕ) (hM : T < (M:ℝ)*δ) :
    ∀ᶠ i in atTop, 0 < ⌊δ*n i⌋₊ ∧ 0 < ⌈T*n i⌉₊ ∧ ⌈T*n i⌉₊ ≤ M*⌊δ*n i⌋₊ := by
  filter_upwards [eventually_floor_horizon_covered n hn hT.le hδ M hM,
    hn.eventually (eventually_gt_atTop (0:ℝ))] with i hi hni
  refine ⟨hi.1,?_,?_⟩
  · exact Nat.ceil_pos.mpr (mul_pos hT hni)
  · exact (Nat.ceil_le_floor_add_one _).trans (by omega)
end DirectionalTransience

end

end

end OAI
