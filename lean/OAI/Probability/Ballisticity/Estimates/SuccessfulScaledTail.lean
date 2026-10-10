import Mathlib
import OAI.Probability.Ballisticity.Estimates.CappedMomentTransfer

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma successfulMedian_scaled_tail_comparison {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (z : ℕ → ℝ) (hz0 : ∀ n, 0 < z n) (hz : Tendsto z atTop atTop)
    {u : ℝ} (hu : 0 < u) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
    limsup (fun n => (successfulAverage ν ℓ (H n)).real
      {X | u < medianDeviation ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) (H n) X / z n}) atTop ≤
      (20/p^2) * limsup (fun n => (independentConditionedPairLaw ν ℓ).real
        {P | u/10 < partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n) / z n}) atTop := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
  let b : ℕ → ℝ := fun j => (recordMedian ν ℓ hp f j:ℝ)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) := independentConditionedPairLaw_probability ν ℓ hp
  have hp0 : 0 < p := ENNReal.toReal_pos hp (measure_ne_top _ _)
  have h1 := successfulAverage_tube_transfer ν hue e f htrans b H hH (fun n => u*z n) (hz.const_mul_atTop hu)
  have h2 := limsup_le_mul_of_bounded_nonneg
    (fun n => (conditionedLaw ν ℓ).real (MedianTubeFailure ℓ f b (H n) (u*z n/10)))
    (fun n => (independentConditionedPairLaw ν ℓ).real {P | u*z n/10 < partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n)})
    (C := 2/p^2) (B := 1) (by positivity)
    (fun _ => measureReal_nonneg) (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one) (by
      intro n
      rw [← medianDeviation_tail]
      exact medianDeviation_conditioned_tail ν e f htrans (H n) (div_pos (mul_pos hu (hz0 n)) (by norm_num)))
  have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 10))
  have hleft (n) : {X | u < medianDeviation ℓ f b (H n) X / z n} = MedianTubeFailure ℓ f b (H n) (u*z n) := by
    rw [← medianDeviation_tail]
    ext X
    exact (lt_div_iff₀ (hz0 n))
  have hright (n) : {P | u/10 < partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n) / z n} =
      {P | u*z n/10 < partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n)} := by
    ext P
    rw [Set.mem_ofPred_eq,Set.mem_ofPred_eq,lt_div_iff₀ (hz0 n),div_mul_eq_mul_div₀]
  change limsup (fun n => (successfulAverage ν ℓ (H n)).real {X | u < medianDeviation ℓ f b (H n) X/z n}) atTop ≤
    (20/p^2) * limsup (fun n => (independentConditionedPairLaw ν ℓ).real
      {P | u/10 < partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n) / z n}) atTop
  simp only [hleft,hright]
  calc
    _ ≤ 10 * ((2/p^2) * limsup (fun n => (independentConditionedPairLaw ν ℓ).real
      {P | u*z n/10 < partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n)}) atTop) := h3
    _ = _ := by ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

noncomputable def unitCap (x : ℝ) : unitInterval :=
  ⟨min (max x 0) 1,le_min (le_max_right _ _) zero_le_one,min_le_right _ _⟩

lemma continuous_unitCap : Continuous unitCap := by
  apply Continuous.subtype_mk
  exact (continuous_id.max continuous_const).min continuous_const

lemma unitCap_tail {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (x : ℝ) :
    u < (unitCap x : ℝ) ↔ u < x := by
  change u < min (max x 0) 1 ↔ _
  rw [lt_min_iff,lt_max_iff]
  simp only [not_lt.mpr hu.le,or_false,hu1,and_true]

lemma unitCap_coe_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (unitCap x : ℝ) = min x 1 := by simp [unitCap,max_eq_left hx]

noncomputable def unitCapLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X) :
    ProbabilityMeasure unitInterval :=
  ⟨μ.map (unitCap ∘ X),⟨by
    rw [Measure.map_apply (continuous_unitCap.measurable.comp hX) MeasurableSet.univ,
      Set.preimage_univ,measure_univ]⟩⟩

lemma unitCapLaw_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    (unitCapLaw μ X hX : Measure unitInterval).real {x | u < (x:ℝ)} = μ.real {x | u < X x} := by
  change (μ.map (unitCap ∘ X)).real _ = _
  unfold Measure.real
  rw [Measure.map_apply (continuous_unitCap.measurable.comp hX)
    (measurableSet_lt measurable_const measurable_subtype_coe)]
  have he : (unitCap ∘ X) ⁻¹' {x | u < (x:ℝ)} = {x | u < X x} := by
    ext x
    exact unitCap_tail hu hu1 (X x)
  rw [he]

lemma unitCapLaw_tail_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    {u : ℝ} (hu : 0 < u) :
    (unitCapLaw μ X hX : Measure unitInterval).real {x | u < (x:ℝ)} ≤ μ.real {x | u < X x} := by
  by_cases hu1 : u < 1
  · exact le_of_eq (unitCapLaw_tail μ X hX hu hu1)
  · have hh : {x : unitInterval | u < (x:ℝ)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_lt.mpr (x.2.2.trans (le_of_not_gt hu1))) hx
    simp only [hh,measureReal_empty]
    exact measureReal_nonneg

lemma unitCapLaw_integral_tail_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ x, 0 ≤ X x) {A : ℝ} (hA : 0 < A) (hA1 : A < 1) :
    (∫ x, unitTailSquare A x ∂(unitCapLaw μ X hX : Measure unitInterval)) =
      ∫ x, (if A < X x then (min (X x) 1)^2 else 0) ∂μ := by
  rw [show (unitCapLaw μ X hX : Measure unitInterval) = μ.map (unitCap ∘ X) from rfl,
    integral_map (continuous_unitCap.measurable.comp hX).aemeasurable
      (unitTailSquare_measurable A).aestronglyMeasurable]
  congr 1
  funext x
  simp only [Function.comp_apply,unitTailSquare]
  simp only [unitCap_tail hA hA1]
  rw [unitCap_coe_of_nonneg (hX0 x)]

lemma raw_capped_tail_moment_transfer {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : ℕ → Measure Ω) (ν : ℕ → Measure Ξ)
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (X : ℕ → Ω → ℝ) (Y : ℕ → Ξ → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hX0 : ∀ n x, 0 ≤ X n x) (hY0 : ∀ n y, 0 ≤ Y n y)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (ht : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∀ u > 0,
      limsup (fun n => (μ (ns n)).real {x | u < X (ns n) x}) atTop ≤
      C * limsup (fun n => (ν (ns n)).real {y | u/D < Y (ns n) y}) atTop)
    {A : ℝ} (hA : 0 < A) (hA1 : A < 1) :
    limsup (fun n => ∫ x, (if A < X n x then (min (X n x) 1)^2 else 0) ∂μ n) atTop ≤
      (8*C*D^2) * limsup (fun n => ∫ y, (if A/(4*D) < Y n y then (min (Y n y) 1)^2 else 0) ∂ν n) atTop := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  let μs := fun n => unitCapLaw (μ n) (X n) (hX n)
  let νs := fun n => unitCapLaw (ν n) (Y n) (hY n)
  have hh := compact_tail_square_moment_transfer μs νs hC hD0 (by
    intro ns hns u hu hu1
    have hh := ht ns hns u hu
    have hud : u/D < 1 := (div_lt_one hD0).mpr (hu1.trans_le hD)
    simpa only [μs,νs,unitCapLaw_tail _ _ _ hu hu1,
      unitCapLaw_tail _ _ _ (div_pos hu hD0) hud] using hh) hA hA1.le
  have had0 : 0 < A/(4*D) := by positivity
  have had1 : A/(4*D) < 1 := (div_lt_one (by positivity)).mpr (by nlinarith)
  simpa only [μs,νs,unitCapLaw_integral_tail_square _ _ _ (hX0 _) hA hA1,
    unitCapLaw_integral_tail_square _ _ _ (hY0 _) had0 had1] using hh

end DirectionalTransience

end

end

end OAI
