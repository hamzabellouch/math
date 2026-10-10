import Mathlib
import OAI.Probability.Ballisticity.Estimates.MomentRescaling
import OAI.Probability.Ballisticity.Estimates.SuccessfulScaledTail

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma capExcess_zero_one (x : unitInterval) : capExcessTest 0 1 x = (x:ℝ)^2 := by
  simp [capExcessTest,min_eq_left x.2.2,max_eq_left (sq_nonneg (x:ℝ))]

lemma capExcess_zero_le_scaled (x : unitInterval) {D : ℝ} (hD : 0 ≤ D) :
    capExcessTest 0 D x ≤ D^2*(x:ℝ)^2 := by
  have hx := x.2.1
  have h0 : 0 ≤ min (D*(x:ℝ)) 1 := le_min (mul_nonneg hD hx) zero_le_one
  change max ((min (D*(x:ℝ)) 1)^2-0^2) 0 ≤ _
  simp only [zero_pow (by norm_num : 2 ≠ 0),sub_zero,max_eq_left (sq_nonneg _)]
  nlinarith [min_le_left (D*(x:ℝ)) 1]

lemma unitCapLaw_integral_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ x, 0 ≤ X x) :
    (∫ x : unitInterval, (x:ℝ)^2 ∂(unitCapLaw μ X hX : Measure unitInterval)) =
    ∫ x, (min (X x) 1)^2 ∂μ := by
  have hc : Continuous (fun x : unitInterval => (x:ℝ)^2) := continuous_subtype_val.pow 2
  rw [show (unitCapLaw μ X hX : Measure unitInterval) = μ.map (unitCap ∘ X) from rfl,
    integral_map (continuous_unitCap.measurable.comp hX).aemeasurable hc.aestronglyMeasurable]
  congr 1
  funext x
  simp only [Function.comp_apply,unitCap_coe_of_nonneg (hX0 x)]

lemma raw_capped_moment_transfer {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : ℕ → Measure Ω) (ν : ℕ → Measure Ξ)
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (X : ℕ → Ω → ℝ) (Y : ℕ → Ξ → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hX0 : ∀ n x, 0 ≤ X n x) (hY0 : ∀ n y, 0 ≤ Y n y)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (ht : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∀ u > 0,
      limsup (fun n => (μ (ns n)).real {x | u < X (ns n) x}) atTop ≤
      C * limsup (fun n => (ν (ns n)).real {y | u/D < Y (ns n) y}) atTop) :
    limsup (fun n => ∫ x, (min (X n x) 1)^2 ∂μ n) atTop ≤
      (4*C*D^2) * limsup (fun n => ∫ y, (min (Y n y) 1)^2 ∂ν n) atTop := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  let μs := fun n => unitCapLaw (μ n) (X n) (hX n)
  let νs := fun n => unitCapLaw (ν n) (Y n) (hY n)
  have hh := compact_capped_moment_transfer μs νs hC hD0 (by
    intro ns hns u hu hu1
    have hh := ht ns hns u hu
    have hud : u/D < 1 := (div_lt_one hD0).mpr (hu1.trans_le hD)
    simpa only [μs,νs,unitCapLaw_tail _ _ _ hu hu1,
      unitCapLaw_tail _ _ _ (div_pos hu hD0) hud] using hh) 0 le_rfl
  have hsqint (p : ProbabilityMeasure unitInterval) : Integrable (fun x : unitInterval => (x:ℝ)^2) (p : Measure unitInterval) :=
    (continuous_subtype_val.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs (p : ProbabilityMeasure unitInterval) : (∫ x : unitInterval, (x:ℝ)^2 ∂(p : Measure unitInterval)) ≤ 1 := by
    calc
      _ ≤ ∫ x : unitInterval, (1:ℝ) ∂(p : Measure unitInterval) := integral_mono (hsqint p) (integrable_const _) (fun x => by
        have h0 := x.2.1; have h1 := x.2.2; nlinarith)
      _ = 1 := by simp
  have hk := limsup_le_mul_of_bounded_nonneg
    (fun n => ∫ x, capExcessTest 0 (2*D) x ∂(νs n : Measure unitInterval))
    (fun n => ∫ x : unitInterval, (x:ℝ)^2 ∂(νs n : Measure unitInterval))
    (sq_nonneg _) (fun n => integral_nonneg (capExcessTest_nonneg _ _))
    (fun n => integral_nonneg (fun _ => sq_nonneg _)) (fun n => hs (νs n)) (by
      intro n
      rw [← integral_const_mul]
      exact integral_mono (capExcess_integrable _ _ _) ((hsqint _).const_mul _) (fun x => capExcess_zero_le_scaled x (by positivity)))
  have hm := hh.trans (mul_le_mul_of_nonneg_left hk hC)
  simp only [capExcess_zero_one] at hm
  simp only [μs,νs,unitCapLaw_integral_square _ _ _ (hX0 _),unitCapLaw_integral_square _ _ _ (hY0 _)] at hm
  nlinarith only [hm]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma successfulMedian_unit_moment_transfer {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (z : ℕ → ℝ) (hz0 : ∀ n, 0 < z n) (hz : Tendsto z atTop atTop) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
    let X := fun n X => medianDeviation ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) (H n) X / z n
    let Y := fun n P => partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n) / z n
    (limsup (fun n => ∫ x, (min (X n x) 1)^2 ∂successfulAverage ν ℓ (H n)) atTop ≤
      (8000/p^2) * limsup (fun n => ∫ y, (min (Y n y) 1)^2 ∂independentConditionedPairLaw ν ℓ) atTop) ∧
    (∀ A, 0 < A → A < 1 →
      limsup (fun n => ∫ x, (if A < X n x then (min (X n x) 1)^2 else 0) ∂successfulAverage ν ℓ (H n)) atTop ≤
      (16000/p^2) * limsup (fun n => ∫ y, (if A/40 < Y n y then (min (Y n y) 1)^2 else 0) ∂independentConditionedPairLaw ν ℓ) atTop) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
  let b : ℕ → ℝ := fun j => (recordMedian ν ℓ hp f j:ℝ)
  let X := fun n X => medianDeviation ℓ f b (H n) X / z n
  let Y := fun n P => partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n) / z n
  let μ := fun n => successfulAverage ν ℓ (H n)
  let υ := fun _ : ℕ => independentConditionedPairLaw ν ℓ
  have hμ : ∀ n, IsProbabilityMeasure (μ n) := fun n => successfulAverage_probability ν hue ℓ (signed_direction_unit e) htrans (H n)
  have hυ : ∀ n, IsProbabilityMeasure (υ n) := fun _ => independentConditionedPairLaw_probability ν ℓ hp
  have hp0 : 0 < p := ENNReal.toReal_pos hp (measure_ne_top _ _)
  have hmX (n) : Measurable (X n) := (measurable_medianDeviation ℓ f b (H n)).div_const _
  have hmY (n) : Measurable (Y n) :=
    (measurable_partialSumMax (commonIncrementProcess ℓ f) (measurable_commonIncrementProcess ℓ f) (H n)).div_const _
  have hX0 (n) (x) : 0 ≤ X n x := div_nonneg (medianDeviation_nonneg _ _ _ _ _) (hz0 n).le
  have hY0 (n) (y) : 0 ≤ Y n y := div_nonneg (partialSumMax_nonneg _ _) (hz0 n).le
  have ht : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∀ u > 0,
      limsup (fun n => (μ (ns n)).real {x | u < X (ns n) x}) atTop ≤
      (20/p^2) * limsup (fun n => (υ (ns n)).real {y | u/10 < Y (ns n) y}) atTop := by
    intro ns hns u hu
    exact successfulMedian_scaled_tail_comparison ν hue e f htrans (H ∘ ns) (hH.comp hns)
      (z ∘ ns) (fun n => hz0 (ns n)) (hz.comp hns) hu
  constructor
  · have hh := @raw_capped_moment_transfer _ _ _ _ μ υ hμ hυ X Y hmX hmY hX0 hY0 (20/p^2) 10 (by positivity) (by norm_num) ht
    change limsup (fun n => ∫ x, (min (X n x) 1)^2 ∂μ n) atTop ≤
      (8000/p^2) * limsup (fun n => ∫ y, (min (Y n y) 1)^2 ∂υ n) atTop
    convert hh using 1
    ring
  · intro A hA hA1
    have hh := @raw_capped_tail_moment_transfer _ _ _ _ μ υ hμ hυ X Y hmX hmY hX0 hY0 (20/p^2) 10 (by positivity) (by norm_num) ht A hA hA1
    change limsup (fun n => ∫ x, (if A < X n x then (min (X n x) 1)^2 else 0) ∂μ n) atTop ≤
      (16000/p^2) * limsup (fun n => ∫ y, (if A/40 < Y n y then (min (Y n y) 1)^2 else 0) ∂υ n) atTop
    norm_num only at hh
    convert hh using 1
    ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma successfulMedian_moment_transfer {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (z : ℕ → ℝ) (hz0 : ∀ n, 0 < z n) (hz : Tendsto z atTop atTop)
    {A L : ℝ} (hA : 0 < A) (hAL : A < L) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
    let X := fun n X => medianDeviation ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) (H n) X / z n
    let Y := fun n P => partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n) / z n
    (limsup (fun n => cappedMoment (successfulAverage ν ℓ (H n)) (X n) L) atTop ≤
      (8000/p^2) * limsup (fun n => cappedMoment (independentConditionedPairLaw ν ℓ) (Y n) L) atTop) ∧
    (limsup (fun n => cappedTailMoment (successfulAverage ν ℓ (H n)) (X n) A L) atTop ≤
      (16000/p^2) * limsup (fun n => cappedTailMoment (independentConditionedPairLaw ν ℓ) (Y n) (A/40) L) atTop) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
  let b : ℕ → ℝ := fun j => (recordMedian ν ℓ hp f j:ℝ)
  let X := fun n X => medianDeviation ℓ f b (H n) X / z n
  let Y := fun n P => partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n) / z n
  let μ := fun n => successfulAverage ν ℓ (H n)
  let υ := fun _ : ℕ => independentConditionedPairLaw ν ℓ
  have hμ : ∀ n, IsProbabilityMeasure (μ n) := fun n => successfulAverage_probability ν hue ℓ (signed_direction_unit e) htrans (H n)
  have hυ : ∀ n, IsProbabilityMeasure (υ n) := fun _ => independentConditionedPairLaw_probability ν ℓ hp
  have hmX (n) : Measurable (X n) := (measurable_medianDeviation ℓ f b (H n)).div_const _
  have hmY (n) : Measurable (Y n) :=
    (measurable_partialSumMax (commonIncrementProcess ℓ f) (measurable_commonIncrementProcess ℓ f) (H n)).div_const _
  have hX0 (n) (x) : 0 ≤ X n x := div_nonneg (medianDeviation_nonneg _ _ _ _ _) (hz0 n).le
  have hY0 (n) (y) : 0 ≤ Y n y := div_nonneg (partialSumMax_nonneg _ _) (hz0 n).le
  have hL : 0 < L := hA.trans hAL
  have hh := successfulMedian_unit_moment_transfer ν hue e f htrans H hH
    (fun n => L*z n) (fun n => mul_pos hL (hz0 n)) (hz.const_mul_atTop hL)
  have h1 : limsup (fun n => cappedMoment (μ n) (fun x => X n x/L) 1) atTop ≤
      (8000/p^2)*limsup (fun n => cappedMoment (υ n) (fun y => Y n y/L) 1) atTop := by
    simpa only [cappedMoment,X,Y,b,μ,υ,div_div,mul_comm] using hh.1
  have h2 : limsup (fun n => cappedTailMoment (μ n) (fun x => X n x/L) (A/L) 1) atTop ≤
      (16000/p^2)*limsup (fun n => cappedTailMoment (υ n) (fun y => Y n y/L) ((A/40)/L) 1) atTop := by
    have haL : 0 < A/L := div_pos hA hL
    have haL1 : A/L < 1 := (div_lt_one hL).mpr hAL
    simpa only [cappedTailMoment,X,Y,b,μ,υ,div_div,mul_comm] using hh.2 (A/L) haL haL1
  change (limsup (fun n => cappedMoment (μ n) (X n) L) atTop ≤
      (8000/p^2) * limsup (fun n => cappedMoment (υ n) (Y n) L) atTop) ∧
    (limsup (fun n => cappedTailMoment (μ n) (X n) A L) atTop ≤
      (16000/p^2) * limsup (fun n => cappedTailMoment (υ n) (Y n) (A/40) L) atTop)
  constructor
  · rw [@limsup_cappedMoment_scale _ _ μ hμ X hmX hX0 L hL,
      @limsup_cappedMoment_scale _ _ υ hυ Y hmY hY0 L hL]
    calc
      _ ≤ L^2*((8000/p^2)*_) := mul_le_mul_of_nonneg_left h1 (sq_nonneg L)
      _ = _ := by ring
  · rw [@limsup_cappedTailMoment_scale _ _ μ hμ X hmX hX0 A L hL,
      @limsup_cappedTailMoment_scale _ _ υ hυ Y hmY hY0 (A/40) L hL]
    calc
      _ ≤ L^2*((16000/p^2)*_) := mul_le_mul_of_nonneg_left h2 (sq_nonneg L)
      _ = _ := by ring

end DirectionalTransience

end

end

end OAI
