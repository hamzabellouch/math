import Mathlib
import OAI.Probability.Ballisticity.Stationary.CompactCapTransfer

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma limsup_le_mul_of_bounded_nonneg (F G : ℕ → ℝ) {C B : ℝ}
    (hC : 0 ≤ C) (hF : ∀ n, 0 ≤ F n) (hG : ∀ n, 0 ≤ G n)
    (hG1 : ∀ n, G n ≤ B) (hFG : ∀ n, F n ≤ C*G n) :
    limsup F atTop ≤ C*limsup G atTop := by
  have hGb : IsBoundedUnder (· ≤ ·) atTop G := isBoundedUnder_of ⟨B,hG1⟩
  have hCb : IsBoundedUnder (· ≤ ·) atTop (fun n => C*G n) :=
    isBoundedUnder_of ⟨C*B,fun n => mul_le_mul_of_nonneg_left (hG1 n) hC⟩
  have hh := limsup_le_limsup (Eventually.of_forall hFG)
    (isCoboundedUnder_le_of_le atTop hF) hCb
  have hm := limsup_mul_le (u := fun _ : ℕ => C) (v := G)
    (Eventually.of_forall fun _ => hC).frequently
    (isBoundedUnder_of ⟨C,fun _ => le_rfl⟩)
    (Eventually.of_forall hG) hGb
  simp only [limsup_const] at hm
  exact hh.trans hm

noncomputable def unitTailSquare (a : ℝ) (x : unitInterval) : ℝ :=
  if a < (x:ℝ) then (x:ℝ)^2 else 0

lemma unitTailSquare_bounds (a : ℝ) (x : unitInterval) :
    0 ≤ unitTailSquare a x ∧ unitTailSquare a x ≤ 1 := by
  have hx0 := x.2.1
  have hx1 := x.2.2
  unfold unitTailSquare
  split_ifs <;> constructor <;> nlinarith

lemma unitTailSquare_measurable (a : ℝ) : Measurable (unitTailSquare a) := by
  exact Measurable.ite (measurableSet_lt measurable_const measurable_subtype_coe)
    (measurable_subtype_coe.pow_const 2) measurable_const

lemma unitTailSquare_integrable (a : ℝ) (μ : ProbabilityMeasure unitInterval) :
    Integrable (unitTailSquare a) (μ : Measure unitInterval) := by
  apply (integrable_const (1:ℝ)).mono' (unitTailSquare_measurable a).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_of_nonneg (unitTailSquare_bounds a x).1]
    exact (unitTailSquare_bounds a x).2)

lemma unitTailSquare_integral_bounds (a : ℝ) (μ : ProbabilityMeasure unitInterval) :
    0 ≤ (∫ x, unitTailSquare a x ∂(μ : Measure unitInterval)) ∧
    (∫ x, unitTailSquare a x ∂(μ : Measure unitInterval)) ≤ 1 := by
  constructor
  · exact integral_nonneg fun x => (unitTailSquare_bounds a x).1
  · calc
      _ ≤ ∫ x : unitInterval, (1:ℝ) ∂(μ : Measure unitInterval) :=
        integral_mono (unitTailSquare_integrable a μ) (integrable_const _)
          (fun x => (unitTailSquare_bounds a x).2)
      _ = 1 := by simp

lemma compact_tail_square_moment_transfer
    (μs νs : ℕ → ProbabilityMeasure unitInterval)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (ht : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∀ u > 0, u < 1 →
      limsup (fun n => (μs (ns n) : Measure unitInterval).real {x | u < (x:ℝ)}) atTop ≤
      C * limsup (fun n => (νs (ns n) : Measure unitInterval).real {y | u/D < (y:ℝ)}) atTop)
    {A : ℝ} (hA : 0 < A) (hA1 : A ≤ 1) :
    limsup (fun n => ∫ x, unitTailSquare A x ∂(μs n : Measure unitInterval)) atTop ≤
      (8*C*D^2) * limsup (fun n => ∫ y, unitTailSquare (A/(4*D)) y ∂(νs n : Measure unitInterval)) atTop := by
  have h1 := limsup_le_mul_of_bounded_nonneg
    (fun n => ∫ x, unitTailSquare A x ∂(μs n : Measure unitInterval))
    (fun n => ∫ x, capExcessTest (A/2) 1 x ∂(μs n : Measure unitInterval))
    (C := 2) (B := 1) (by norm_num)
    (fun n => (unitTailSquare_integral_bounds A (μs n)).1)
    (fun n => (capExcess_integral_bounds (A/2) zero_le_one (μs n)).1)
    (fun n => (capExcess_integral_bounds (A/2) zero_le_one (μs n)).2) (by
      intro n
      rw [← integral_const_mul]
      exact integral_mono (unitTailSquare_integrable A _) ((capExcess_integrable _ _ _).const_mul _)
        (fun x => capped_tail_le_excess x hA hA1))
  have h2 := compact_capped_moment_transfer μs νs hC hD ht (A/2) (by positivity)
  have h3 := limsup_le_mul_of_bounded_nonneg
    (fun n => ∫ y, capExcessTest (A/2) (2*D) y ∂(νs n : Measure unitInterval))
    (fun n => ∫ y, unitTailSquare (A/(4*D)) y ∂(νs n : Measure unitInterval))
    (C := (2*D)^2) (B := 1) (sq_nonneg _)
    (fun n => (capExcess_integral_bounds (A/2) (by positivity) (νs n)).1)
    (fun n => (unitTailSquare_integral_bounds _ (νs n)).1)
    (fun n => (unitTailSquare_integral_bounds _ (νs n)).2) (by
      intro n
      rw [← integral_const_mul]
      apply integral_mono (capExcess_integrable _ _ _) ((unitTailSquare_integrable _ _).const_mul _)
      intro y
      have he : A/2/(2*D) = A/(4*D) := by ring
      simpa only [he,unitTailSquare] using capExcess_le_scaled_tail y (by positivity : 0 ≤ A/2) (by positivity : 0 < 2*D))
  calc
    _ ≤ 2*(C*(((2*D)^2)*limsup (fun n => ∫ y, unitTailSquare (A/(4*D)) y ∂(νs n : Measure unitInterval)) atTop)) :=
      h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hC)) (by norm_num))
    _ = _ := by ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def medianDeviation {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) : ℕ → Path d → ℝ
  | 0, X => |signedCoordinate f (recordIndexPosition ℓ 0 X)-b 0|
  | H+1, X => max (medianDeviation ℓ f b H X)
      |signedCoordinate f (recordIndexPosition ℓ (H+1) X)-b (H+1)|

lemma medianDeviation_nonneg {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (H : ℕ) (X : Path d) : 0 ≤ medianDeviation ℓ f b H X := by
  cases H with
  | zero => exact abs_nonneg _
  | succ H => exact (abs_nonneg _).trans (le_max_right _ _)

lemma measurable_medianDeviation {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (H : ℕ) : Measurable (medianDeviation ℓ f b H) := by
  induction H with
  | zero => exact (((measurable_of_countable (signedCoordinate f)).comp
      (measurable_recordIndexPosition ℓ 0)).sub_const (b 0)).abs
  | succ H ih => exact ih.max ((((measurable_of_countable (signedCoordinate f)).comp
      (measurable_recordIndexPosition ℓ (H+1))).sub_const (b (H+1))).abs)

lemma medianDeviation_tail {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (H : ℕ) (z : ℝ) :
    {X | z < medianDeviation ℓ f b H X} = MedianTubeFailure ℓ f b H z := by
  ext X
  induction H with
  | zero => simp [medianDeviation,MedianTubeFailure]
  | succ H ih =>
    change z < max _ _ ↔ ∃ j ≤ H+1, z < _
    change z < medianDeviation ℓ f b H X ↔ ∃ j ≤ H, z < _ at ih
    rw [lt_max_iff,ih]
    constructor
    · rintro (⟨j,hj,h⟩ | h)
      · exact ⟨j,by omega,h⟩
      · exact ⟨H+1,le_rfl,h⟩
    · rintro ⟨j,hj,h⟩
      by_cases he : j = H+1
      · exact Or.inr (he ▸ h)
      · exact Or.inl ⟨j,by omega,h⟩

lemma medianDeviation_conditioned_tail {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H : ℕ) {z : ℝ} (hz : 0 < z) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
    (conditionedLaw ν ℓ).real {X | z < medianDeviation ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) H X} ≤
      (2/p^2) * (independentConditionedPairLaw ν ℓ).real
        {P | z < partialSumMax (fun n => commonIncrementProcess ℓ f n P) H} := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
  have hp0 : 0 < p := ENNReal.toReal_pos hp (measure_ne_top _ _)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ hp
  rw [medianDeviation_tail]
  have he : MedianTubeFailure ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) H z =ᵐ[conditionedLaw ν ℓ]
      {X | ∃ j, 0 < j ∧ j ≤ H ∧ z < |signedCoordinate f (recordIndexPosition ℓ j X)-(recordMedian ν ℓ hp f j:ℝ)|} := by
    filter_upwards [(conditionedLaw_absolutelyContinuous ν ℓ).ae_le (annealed_initial ν)] with X hX
    apply propext
    constructor
    · rintro ⟨j,hj,hbad⟩
      have hj0 : 0 < j := by
        by_contra hn
        have hjz : j = 0 := by omega
        simp [hjz,recordIndexPosition,recordIndexTime_zero,hX,recordMedian_zero,signedCoordinate] at hbad
        linarith
      exact ⟨j,hj0,hj,hbad⟩
    · rintro ⟨j,_,hj,hbad⟩
      exact ⟨j,hj,hbad⟩
  rw [measureReal_congr he]
  have hh := conditioned_firstHit_median_maximum ν ℓ htrans (signedHeight e)
    (signedHeight_projection e) (signedHeight_step_le e) f H z
  have hh' := ENNReal.toReal_mono (measure_ne_top _ _) hh
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_pow] at hh'
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] at hh'
  change p^2*(1/2)*(conditionedLaw ν ℓ).real _ ≤ (independentConditionedPairLaw ν ℓ).real _ at hh'
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hp0)).mpr
  nlinarith

end DirectionalTransience

end

end

end OAI
