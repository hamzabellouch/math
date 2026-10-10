import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingWeightTests
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.SamplingWeights

def testedProduct (endpoint : Bool) (D I : Finset ℕ) (h α : ℝ)
    (E F : ℕ → Set ℝ) (θ : ℕ → ℝ) (n : ℕ) (x : Base) : ℝ :=
  ∏ i ∈ D, testedCoordinateWeight endpoint I h α i (E i) (F i)
    (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i))

def testedIdeal (endpoint : Bool) (D I : Finset ℕ) (h α : ℝ)
    (E F : ℕ → Set ℝ) (x : Base) : ℝ :=
  ∏ i ∈ D, ∫ t in (0 : ℝ)..1,
    testedCoordinateWeight endpoint I h α i (E i) (F i)
      (circleRepresentative (x i)) t

private theorem measurable_scalarProduct_pair (D : Finset ℕ)
    (u : ℕ → ℝ → ℝ → ℝ)
    (hu : ∀ i ∈ D, Measurable (fun p : ℝ × ℝ => u i p.1 p.2)) (n : ℕ) :
    Measurable (fun z : (ℕ → ℝ) × Base =>
      ∏ i ∈ D, u i (circleRepresentative (z.2 i)) (Int.fract ((n : ℝ) * z.1 i))) := by
  apply Finset.measurable_prod D
  intro i hi
  have hs : Measurable (fun z : (ℕ → ℝ) × Base => circleRepresentative (z.2 i)) :=
    ProductCocycle.measurable_representative.comp ((measurable_pi_apply i).comp measurable_snd)
  have ht : Measurable (fun z : (ℕ → ℝ) × Base => Int.fract ((n : ℝ) * z.1 i)) :=
    (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).fract
  exact (hu i hi).comp (hs.prodMk ht)

theorem measurable_testedProduct_pair (endpoint : Bool) (D I : Finset ℕ) (h α : ℝ)
    (E F : ℕ → Set ℝ) (hE : ∀ i ∈ D, MeasurableSet (E i))
    (hF : ∀ i ∈ D, MeasurableSet (F i)) (n : ℕ) :
    Measurable (fun z : (ℕ → ℝ) × Base =>
      testedProduct endpoint D I h α E F z.1 n z.2) := by
  exact measurable_scalarProduct_pair D
    (fun i => testedCoordinateWeight endpoint I h α i (E i) (F i))
    (fun i hi => measurable_testedCoordinateWeight endpoint I h α i (hE i hi) (hF i hi)) n

theorem testedProduct_bounds (endpoint : Bool) (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (E F : ℕ → Set ℝ)
    (θ : ℕ → ℝ) (n : ℕ) (x : Base) :
    0 ≤ testedProduct endpoint D I h α E F θ n x ∧
      testedProduct endpoint D I h α E F θ n x ≤ height h α ^ D.card := by
  constructor
  · exact Finset.prod_nonneg fun i _ =>
      (testedCoordinateWeight_bounds endpoint I hh hα i (E i) (F i) _ _).1
  · calc
      _ ≤ ∏ _i ∈ D, height h α := Finset.prod_le_prod₀
        (fun i _ => (testedCoordinateWeight_bounds endpoint I hh hα i (E i) (F i) _ _).1)
        (fun i _ => (testedCoordinateWeight_bounds endpoint I hh hα i (E i) (F i) _ _).2)
      _ = _ := by simp

theorem memLp_testedProduct_pair (endpoint : Bool) (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (E F : ℕ → Set ℝ)
    (hE : ∀ i ∈ D, MeasurableSet (E i)) (hF : ∀ i ∈ D, MeasurableSet (F i))
    (n : ℕ) (ν : Measure (ℕ → ℝ)) [IsFiniteMeasure ν] (p : ℝ≥0∞) :
    MemLp (fun z : (ℕ → ℝ) × Base => testedProduct endpoint D I h α E F z.1 n z.2)
      p (ν.prod baseMeasure) := by
  apply MemLp.of_bound
    (measurable_testedProduct_pair endpoint D I h α E F hE hF n).aestronglyMeasurable
    (height h α ^ D.card)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (testedProduct_bounds endpoint D I hh hα E F z.1 n z.2).1]
  exact (testedProduct_bounds endpoint D I hh hα E F z.1 n z.2).2

theorem stronglyMeasurable_testedAverage (endpoint : Bool) (I : Finset ℕ) (h α : ℝ)
    (i : ℕ) {E F : Set ℝ} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    StronglyMeasurable (fun s => ∫ t in (0 : ℝ)..1,
      testedCoordinateWeight endpoint I h α i E F s t) := by
  have hm := (measurable_testedCoordinateWeight endpoint I h α i hE hF).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hm

theorem norm_testedAverage_le (endpoint : Bool) (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) (E F : Set ℝ) (s : ℝ) :
    ‖∫ t in (0 : ℝ)..1, testedCoordinateWeight endpoint I h α i E F s t‖ ≤
      height h α := by
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖testedCoordinateWeight endpoint I h α i E F s t‖ ≤ height h α := by
    intro t _
    rw [Real.norm_eq_abs, abs_of_nonneg (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).1]
    exact (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).2
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb

theorem memLp_testedIdeal (endpoint : Bool) (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (E F : ℕ → Set ℝ)
    (hE : ∀ i ∈ D, MeasurableSet (E i)) (hF : ∀ i ∈ D, MeasurableSet (F i))
    (p : ℝ≥0∞) : MemLp (testedIdeal endpoint D I h α E F) p baseMeasure := by
  have hm : Measurable (testedIdeal endpoint D I h α E F) := by
    unfold testedIdeal
    apply Finset.measurable_prod
    intro i hi
    exact (stronglyMeasurable_testedAverage endpoint I h α i (hE i hi) (hF i hi)).measurable.comp
      (ProductCocycle.measurable_representative.comp (measurable_pi_apply i))
  apply MemLp.of_bound hm.aestronglyMeasurable (height h α ^ D.card)
  filter_upwards [] with x
  unfold testedIdeal
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc
    _ ≤ ∏ _i ∈ D, height h α := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      (fun i _ => by simpa only [Real.norm_eq_abs] using
        norm_testedAverage_le endpoint I hh hα i (E i) (F i) (circleRepresentative (x i)))
    _ = _ := by simp

theorem memLp_testedAverageError_pair (endpoint : Bool) (D I N : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (E F : ℕ → Set ℝ)
    (hE : ∀ i ∈ D, MeasurableSet (E i)) (hF : ∀ i ∈ D, MeasurableSet (F i))
    (ν : Measure (ℕ → ℝ)) [IsFiniteMeasure ν] :
    MemLp (fun z : (ℕ → ℝ) × Base =>
      (N.card : ℝ)⁻¹ * (∑ n ∈ N, testedProduct endpoint D I h α E F z.1 n z.2) -
        testedIdeal endpoint D I h α E F z.2) 2 (ν.prod baseMeasure) := by
  exact ((memLp_finsetSum N (fun n _ =>
    memLp_testedProduct_pair endpoint D I hh hα E F hE hF n ν 2)).const_mul
      ((N.card : ℝ)⁻¹)).sub ((memLp_testedIdeal endpoint D I hh hα E F hE hF 2).comp_snd ν)

theorem integrable_testedAverageError_sq (endpoint : Bool) (D I N : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (E F : ℕ → Set ℝ)
    (hE : ∀ i ∈ D, MeasurableSet (E i)) (hF : ∀ i ∈ D, MeasurableSet (F i))
    (ν : Measure (ℕ → ℝ)) [IsFiniteMeasure ν] :
    Integrable (fun z : (ℕ → ℝ) × Base =>
      ((N.card : ℝ)⁻¹ * (∑ n ∈ N, testedProduct endpoint D I h α E F z.1 n z.2) -
        testedIdeal endpoint D I h α E F z.2) ^ 2) (ν.prod baseMeasure) :=
  (memLp_testedAverageError_pair endpoint D I N hh hα E F hE hF ν).integrable_sq

end Invariant233.ProductModel.SamplingWeights

end

end OAI
