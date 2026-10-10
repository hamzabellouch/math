import Mathlib
import OAI.Probability.SKGap.Entropy.ExponentiallyRare

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKGapCutoff.Regression

noncomputable def positiveRamp (k : ℕ) (x : ℝ) : ℝ := min 1 (max 0 ((k:ℝ)*x))
noncomputable def positiveIndicator (x : ℝ) : ℝ := if 0 < x then 1 else 0
noncomputable def boundaryRamp (k : ℕ) (x : ℝ) : ℝ :=
  1-positiveRamp k x-positiveRamp k (-x)

lemma positiveRamp_bounds (k : ℕ) (x : ℝ) :
    0 ≤ positiveRamp k x ∧ positiveRamp k x ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

lemma positiveRamp_eq_zero {x : ℝ} (hx : x ≤ 0) (k : ℕ) :
    positiveRamp k x = 0 := by
  simp [positiveRamp, max_eq_left (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hx)]

lemma positiveRamp_lipschitz (k : ℕ) : LipschitzWith (k:ℝ≥0) (positiveRamp k) := by
  have hs : LipschitzWith (k:ℝ≥0) (fun x : ℝ => (k:ℝ)*x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ)≤k)]
    rfl
  exact (hs.const_max 0).const_min 1

lemma positiveIndicator_measurable : Measurable positiveIndicator := by
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    measurable_const measurable_const

lemma positiveIndicator_bounds (x : ℝ) : 0 ≤ positiveIndicator x ∧ positiveIndicator x ≤ 1 := by
  unfold positiveIndicator
  split_ifs <;> norm_num

lemma boundaryRamp_bounds (k : ℕ) (x : ℝ) :
    0 ≤ boundaryRamp k x ∧ boundaryRamp k x ≤ 1 := by
  have hp := positiveRamp_bounds k x
  have hn := positiveRamp_bounds k (-x)
  unfold boundaryRamp
  by_cases hx : 0 ≤ x
  · rw [positiveRamp_eq_zero (neg_nonpos.mpr hx)]
    constructor <;> linarith
  · rw [positiveRamp_eq_zero (le_of_lt (lt_of_not_ge hx))]
    constructor <;> linarith

lemma positiveRamp_error (k : ℕ) (x : ℝ) :
    |positiveIndicator x-positiveRamp k x| ≤ boundaryRamp k x := by
  unfold positiveIndicator
  split_ifs with hx
  · rw [boundaryRamp, positiveRamp_eq_zero (neg_nonpos.mpr hx.le), sub_zero,
      abs_of_nonneg (sub_nonneg.mpr (positiveRamp_bounds k x).2)]
  · rw [positiveRamp_eq_zero (le_of_not_gt hx)]
    simpa using (boundaryRamp_bounds k x).1

lemma positiveRamp_tendsto (x : ℝ) :
    Tendsto (fun k => positiveRamp k x) atTop (𝓝 (positiveIndicator x)) := by
  by_cases hx : 0 < x
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ⌈1/x⌉₊] with k hk
    have hkx : 1/x ≤ (k:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    have hkx' : 1 ≤ (k:ℝ)*x := (div_le_iff₀ hx).mp hkx
    simp only [positiveRamp, positiveIndicator, ite_eq_left hx]
    exact (min_eq_left (le_max_of_le_right hkx')).symm
  · simpa only [positiveIndicator, ite_eq_right hx, positiveRamp_eq_zero (le_of_not_gt hx)] using
      (tendsto_const_nhds : Tendsto (fun _k : ℕ => (0:ℝ)) atTop (𝓝 0))

lemma boundaryRamp_tendsto {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun k => boundaryRamp k x) atTop (𝓝 0) := by
  have hh := ((tendsto_const_nhds : Tendsto (fun _k : ℕ => (1:ℝ)) atTop (𝓝 1)).sub
    (positiveRamp_tendsto x)).sub (positiveRamp_tendsto (-x))
  have he : 1-positiveIndicator x-positiveIndicator (-x) = 0 := by
    rcases lt_or_gt_of_ne hx with h | h
    · simp [positiveIndicator, not_lt.mpr h.le, neg_pos.mpr h]
    · simp [positiveIndicator, h, not_lt.mpr (neg_nonpos.mpr h.le)]
  simpa only [he, boundaryRamp] using hh

lemma boundaryRamp_lipschitz (k : ℕ) :
    LipschitzWith (2*(k:ℝ≥0)) (boundaryRamp k) := by
  have hn : LipschitzWith (k:ℝ≥0) (fun x : ℝ => positiveRamp k (-x)) := by
    have hid : LipschitzWith 1 (fun x : ℝ => x) := LipschitzWith.id
    simpa only [mul_one, Function.comp_def, Pi.neg_apply] using
      (positiveRamp_lipschitz k).comp hid.neg
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hp := (positiveRamp_lipschitz k).dist_le_mul x y
  have hq := hn.dist_le_mul x y
  rw [Real.dist_eq] at hp hq ⊢
  have he : boundaryRamp k x-boundaryRamp k y =
      -(positiveRamp k x-positiveRamp k y)-(positiveRamp k (-x)-positiveRamp k (-y)) := by
    unfold boundaryRamp
    ring
  rw [he]
  calc
    _ ≤ |-(positiveRamp k x-positiveRamp k y)|+
      |positiveRamp k (-x)-positiveRamp k (-y)| := abs_sub _ _
    _ ≤ (2*(k:ℝ≥0):ℝ)*dist x y := by
      rw [abs_neg]
      push_cast at hp hq ⊢
      linarith

lemma boundaryRamp_integral_tendsto
    {E : Type*} [MeasurableSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
    (g : E → ℝ) (hg : Measurable g) (hz : ν {x | g x = 0} = 0) :
    Tendsto (fun k => ∫ x, boundaryRamp k (g x) ∂ν) atTop (𝓝 0) := by
  have hne : ∀ᵐ x ∂ν, g x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hz
  have ht : Tendsto (fun k => ∫ x, boundaryRamp k (g x) ∂ν)
      atTop (𝓝 (∫ _x : E, (0:ℝ) ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
    · intro k
      exact ((boundaryRamp_lipschitz k).continuous.measurable.comp hg).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (boundaryRamp_bounds k (g x)).1]
      exact (boundaryRamp_bounds k (g x)).2
    · filter_upwards [hne] with x hx
      exact boundaryRamp_tendsto hx
  simpa using ht

lemma positiveRamp_mul_integral_tendsto
    {E : Type*} [MeasurableSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
    (f g : E → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    Tendsto (fun k => ∫ x, f x*positiveRamp k (g x) ∂ν) atTop
      (𝓝 (∫ x, f x*positiveIndicator (g x) ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => B)
  · intro k
    exact (hf.mul ((positiveRamp_lipschitz k).continuous.measurable.comp hg)).aestronglyMeasurable
  · exact integrable_const _
  · intro k
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (positiveRamp_bounds k (g x)).1]
    exact (mul_le_mul_of_nonneg_left (positiveRamp_bounds k (g x)).2 (abs_nonneg _)).trans
      (by simpa using hB x)
  · filter_upwards [] with x
    exact tendsto_const_nhds.mul (positiveRamp_tendsto (g x))

theorem ExponentialEmpiricalConcentration.threshold_average
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E}
    {ν : Measure E} [IsProbabilityMeasure ν]
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (f g : E → ℝ) {K L B : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hB : ∀ x, |f x| ≤ B) (hz : ν {x | g x = 0} = 0) :
    ExponentialConvergence ρ
      (fun n h => (∑ i, f (X n h i)*positiveIndicator (g (X n h i)))/(n:ℝ))
      (∫ x, f x*positiveIndicator (g x) ∂ν) := by
  intro ε hε
  let D : ℝ := B+1
  have hD : 0 < D := by dsimp [D]; positivity
  let δ := ε/(6*D)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : D*δ = ε/6 := by dsimp [δ]; field_simp
  have hbias : ∀ᶠ k : ℕ in atTop,
      |(∫ x, f x*positiveRamp k (g x) ∂ν) -
        ∫ x, f x*positiveIndicator (g x) ∂ν| < ε/3 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp
      (positiveRamp_mul_integral_tendsto f g hf.continuous.measurable
        hg.continuous.measurable B hB)) (ε/3) (by positivity)
  have hboundary : ∀ᶠ k : ℕ in atTop, |∫ x, boundaryRamp k (g x) ∂ν| < δ := by
    simpa only [Real.dist_eq, sub_zero] using (Metric.tendsto_nhds.mp
      (boundaryRamp_integral_tendsto g hg.continuous.measurable hz)) δ hδ
  obtain ⟨k,hbias,hboundary⟩ := (hbias.and hboundary).exists
  have hramp : LipschitzWith ((k:ℝ≥0)*L) (fun x => positiveRamp k (g x)) :=
    (positiveRamp_lipschitz k).comp hg
  have hbramp : ∀ x, |positiveRamp k (g x)| ≤ (1:ℝ≥0) := by
    intro x
    rw [abs_of_nonneg (positiveRamp_bounds k (g x)).1]
    exact (positiveRamp_bounds k (g x)).2
  have hsmooth := hX.average (fun x => f x*positiveRamp k (g x))
    (bounded_product_lipschitz hf hramp hB hbramp) B (fun x => by
      rw [abs_mul]
      exact (mul_le_mul (hB x) (hbramp x) (abs_nonneg _) B.coe_nonneg).trans (by simp))
  have hb := hX.average (fun x => boundaryRamp k (g x))
    ((boundaryRamp_lipschitz k).comp hg) 1 (fun x => by
      rw [abs_of_nonneg (boundaryRamp_bounds k (g x)).1]
      exact (boundaryRamp_bounds k (g x)).2)
  apply ((hsmooth (ε/3) (by positivity)).union (hb δ hδ)).mono
  refine Filter.Eventually.of_forall ?_
  intro n h hh
  change ε ≤ |(∑ i, f (X n h i)*positiveIndicator (g (X n h i)))/(n:ℝ) -
    ∫ x, f x*positiveIndicator (g x) ∂ν| at hh
  by_cases hs : ε/3 ≤ dist
      ((∑ i, f (X n h i)*positiveRamp k (g (X n h i)))/(n:ℝ))
      (∫ x, f x*positiveRamp k (g x) ∂ν)
  · exact Or.inl hs
  apply Or.inr
  by_contra hb'
  have hsmall : (∑ i, boundaryRamp k (g (X n h i)))/(n:ℝ) < 2*δ := by
    have hh' : |(∑ i, boundaryRamp k (g (X n h i)))/(n:ℝ) -
        ∫ x, boundaryRamp k (g x) ∂ν| < δ := lt_of_not_ge hb'
    have hi := le_abs_self (∫ x, boundaryRamp k (g x) ∂ν)
    have ha := le_abs_self ((∑ i, boundaryRamp k (g (X n h i)))/(n:ℝ) -
      ∫ x, boundaryRamp k (g x) ∂ν)
    linarith
  have herror : |(∑ i, f (X n h i)*positiveIndicator (g (X n h i)))/(n:ℝ) -
      (∑ i, f (X n h i)*positiveRamp k (g (X n h i)))/(n:ℝ)| ≤
      D*((∑ i, boundaryRamp k (g (X n h i)))/(n:ℝ)) := by
    rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n),
      ← Finset.sum_sub_distrib, ← mul_div_assoc, Finset.mul_sum]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro i _
    rw [← mul_sub, abs_mul]
    apply mul_le_mul ((hB _).trans (by dsimp [D]; linarith))
      (positiveRamp_error k _) (abs_nonneg _) hD.le
  have htriangle := abs_add_three
    ((∑ i, f (X n h i)*positiveIndicator (g (X n h i)))/(n:ℝ) -
      (∑ i, f (X n h i)*positiveRamp k (g (X n h i)))/(n:ℝ))
    ((∑ i, f (X n h i)*positiveRamp k (g (X n h i)))/(n:ℝ) -
      ∫ x, f x*positiveRamp k (g x) ∂ν)
    ((∫ x, f x*positiveRamp k (g x) ∂ν) - ∫ x, f x*positiveIndicator (g x) ∂ν)
  rw [sub_add_sub_cancel, sub_add_sub_cancel] at htriangle
  have hs' : |(∑ i, f (X n h i)*positiveRamp k (g (X n h i)))/(n:ℝ) -
      ∫ x, f x*positiveRamp k (g x) ∂ν| < ε/3 := lt_of_not_ge hs
  have herror' : D*((∑ i, boundaryRamp k (g (X n h i)))/(n:ℝ)) < ε/3 := by
    nlinarith
  linarith

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology

end

end OAI
