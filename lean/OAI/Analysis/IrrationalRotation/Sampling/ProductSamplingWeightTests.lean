import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingWeightMeasurability
import OAI.Analysis.IrrationalRotation.Product.ProductOrbitTests

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

namespace Invariant233.ProductModel.SamplingWeights

def testedCoordinateWeight (endpoint : Bool) (I : Finset ℕ) (h α : ℝ) (i : ℕ)
    (E F : Set ℝ) (s t : ℝ) : ℝ :=
  let a := if endpoint then Int.fract (s - t) else s
  let b := if endpoint then s else Int.fract (s + t)
  coordinateWeight I h α i a t * E.indicator (fun _ => 1) a *
    F.indicator (fun _ => 1) b

def rectangle (D : Finset ℕ) (E F : ℕ → Set ℝ) : Set (Base × Base) :=
  {xy | ∀ i ∈ D, circleRepresentative (xy.1 i) ∈ E i ∧
    circleRepresentative (xy.2 i) ∈ F i}

theorem measurable_testedCoordinateWeight (endpoint : Bool) (I : Finset ℕ)
    (h α : ℝ) (i : ℕ) {E F : Set ℝ} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    Measurable (fun p : ℝ × ℝ => testedCoordinateWeight endpoint I h α i E F p.1 p.2) := by
  have he : Measurable (E.indicator (fun _ : ℝ => (1 : ℝ))) :=
    measurable_const.indicator hE
  have hf : Measurable (F.indicator (fun _ : ℝ => (1 : ℝ))) :=
    measurable_const.indicator hF
  cases endpoint
  · exact ((measurable_coordinateWeight I h α i).mul (he.comp measurable_fst)).mul
      (hf.comp (measurable_fst.add measurable_snd).fract)
  · exact (((measurable_coordinateWeight I h α i).comp
      ((measurable_fst.sub measurable_snd).fract.prodMk measurable_snd)).mul
      (he.comp (measurable_fst.sub measurable_snd).fract)).mul
      (hf.comp measurable_fst)

theorem testedCoordinateWeight_bounds (endpoint : Bool) (I : Finset ℕ)
    {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (i : ℕ) (E F : Set ℝ) (s t : ℝ) :
    0 ≤ testedCoordinateWeight endpoint I h α i E F s t ∧
      testedCoordinateWeight endpoint I h α i E F s t ≤ height h α := by
  unfold testedCoordinateWeight
  dsimp only
  by_cases he : (if endpoint = true then Int.fract (s - t) else s) ∈ E
  · by_cases hf : (if endpoint = true then s else Int.fract (s + t)) ∈ F
    · simp only [Set.indicator_of_mem he, Set.indicator_of_mem hf, mul_one]
      exact coordinateWeight_bounds I hh hα i _ _
    · simp only [Set.indicator_of_notMem hf, mul_zero]
      exact ⟨le_rfl, by unfold height; positivity⟩
  · simp only [Set.indicator_of_notMem he, mul_zero, zero_mul]
    exact ⟨le_rfl, by unfold height; positivity⟩

theorem measurableSet_rectangle (D : Finset ℕ) (E F : ℕ → Set ℝ)
    (hE : ∀ i ∈ D, MeasurableSet (E i)) (hF : ∀ i ∈ D, MeasurableSet (F i)) :
    MeasurableSet (rectangle D E F) := by
  unfold rectangle
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro hi
  exact ((ProductCocycle.measurable_representative.comp
    ((measurable_pi_apply i).comp measurable_fst)) (hE i hi)).inter
    ((ProductCocycle.measurable_representative.comp
      ((measurable_pi_apply i).comp measurable_snd)) (hF i hi))

theorem representative_rotation_fract (θ : ℕ → ℝ) (n : ℕ) (x : Base) (i : ℕ) :
    circleRepresentative (rotationIterate θ (n : ℤ) x i) =
      Int.fract (circleRepresentative (x i) + Int.fract ((n : ℝ) * θ i)) := by
  change ProductCocycle.representative (x i + (((n : ℝ) * θ i : ℝ) : Circle)) = _
  rw [ProductCocycle.representative_add, TailTrimming.fract_add_eq_fract_add_fract]
  rfl

theorem first_testedCoordinateWeight_eq (I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) (x : Base) (i : ℕ) (E F : Set ℝ) :
    testedCoordinateWeight false I h α i E F (circleRepresentative (x i))
      (Int.fract ((n : ℝ) * θ i)) =
    if circleRepresentative (x i) ∈ E ∧
        circleRepresentative (rotationIterate θ (n : ℤ) x i) ∈ F then
      coordinateWeight I h α i (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i))
    else 0 := by
  rw [representative_rotation_fract]
  unfold testedCoordinateWeight
  dsimp only
  by_cases he : circleRepresentative (x i) ∈ E <;>
    by_cases hf : Int.fract (circleRepresentative (x i) + (n : ℝ) * θ i) ∈ F <;>
    simp [he, hf]

theorem first_tested_product_eq (D I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) (E F : ℕ → Set ℝ) (x : Base) :
    (∏ i ∈ D, testedCoordinateWeight false I h α i (E i) (F i)
      (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i))) =
    (rectangle D E F).indicator (fun xy => orbitWeight D I h α θ n xy.1)
      (TailTrimming.orbitPairMap θ n x) := by
  simp_rw [first_testedCoordinateWeight_eq]
  rw [Finset.prod_ite_zero]
  simp only [rectangle, Set.indicator_apply, Set.mem_ofPred_eq,
    TailTrimming.orbitPairMap, orbitWeight]

theorem fract_sub_fract (s t : ℝ) :
    Int.fract (s - t) = Int.fract (s - Int.fract t) := by
  have he : s - Int.fract t = s - t + (⌊t⌋ : ℤ) := by
    rw [Int.fract]
    ring
  rw [he, Int.fract_add_intCast]

theorem representative_inverse_rotation_fract (θ : ℕ → ℝ)
    (n : ℕ) (y : Base) (i : ℕ) :
    circleRepresentative (rotationIterate θ (-(n : ℤ)) y i) =
      Int.fract (circleRepresentative (y i) - Int.fract ((n : ℝ) * θ i)) := by
  change ProductCocycle.representative (y i +
    (((-(n : ℤ) : ℤ) : ℝ) * θ i : ℝ)) = _
  rw [ProductCocycle.representative_add, Int.cast_neg, Int.cast_natCast,
    neg_mul, ← sub_eq_add_neg, fract_sub_fract]
  rfl

theorem second_testedCoordinateWeight_eq (I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) (y : Base) (i : ℕ) (E F : Set ℝ) :
    testedCoordinateWeight true I h α i E F (circleRepresentative (y i))
      (Int.fract ((n : ℝ) * θ i)) =
    if circleRepresentative (rotationIterate θ (-(n : ℤ)) y i) ∈ E ∧
        circleRepresentative (y i) ∈ F then
      coordinateWeight I h α i
        (circleRepresentative (rotationIterate θ (-(n : ℤ)) y i))
        (Int.fract ((n : ℝ) * θ i))
    else 0 := by
  rw [representative_inverse_rotation_fract]
  unfold testedCoordinateWeight
  dsimp only
  by_cases he : Int.fract (circleRepresentative (y i) - (n : ℝ) * θ i) ∈ E <;>
    by_cases hf : circleRepresentative (y i) ∈ F <;> simp [he, hf]

theorem second_tested_product_eq (D I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) (E F : ℕ → Set ℝ) (y : Base) :
    (∏ i ∈ D, testedCoordinateWeight true I h α i (E i) (F i)
      (circleRepresentative (y i)) (Int.fract ((n : ℝ) * θ i))) =
    (rectangle D E F).indicator (fun xy => orbitWeight D I h α θ n xy.1)
      (rotationIterate θ (-(n : ℤ)) y, y) := by
  simp_rw [second_testedCoordinateWeight_eq]
  rw [Finset.prod_ite_zero]
  simp only [rectangle, Set.indicator_apply, Set.mem_ofPred_eq, orbitWeight]

theorem orbitTestWeight_eq_first_product (D I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) (E F : ℕ → Set ℝ) (x : Base) :
    TailTrimming.orbitTestWeight θ (rectangle D E F) (orbitWeight D I h α θ) n x =
      ∏ i ∈ D, testedCoordinateWeight false I h α i (E i) (F i)
        (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i)) := by
  simpa only [TailTrimming.orbitTestWeight, Set.indicator_apply, Set.mem_preimage,
    TailTrimming.orbitPairMap] using (first_tested_product_eq D I h α θ n E F x).symm

theorem orbitTestWeight_eq_second_product (D I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) (E F : ℕ → Set ℝ) (y : Base) :
    TailTrimming.orbitTestWeight θ (rectangle D E F) (orbitWeight D I h α θ) n
      (rotationIterate θ (-(n : ℤ)) y) =
      ∏ i ∈ D, testedCoordinateWeight true I h α i (E i) (F i)
        (circleRepresentative (y i)) (Int.fract ((n : ℝ) * θ i)) := by
  rw [TailTrimming.orbitTestWeight_inverse]
  exact (second_tested_product_eq D I h α θ n E F y).symm

theorem tested_first_marginal (D I N : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (θ : ℕ → ℝ) (E F : ℕ → Set ℝ)
    (hE : ∀ i ∈ D, MeasurableSet (E i)) (hF : ∀ i ∈ D, MeasurableSet (F i)) :
    ((TailTrimming.orbitAverageMeasure θ N
      (fun n x => ENNReal.ofReal (orbitWeight D I h α θ n x))).restrict
        (rectangle D E F)).map Prod.fst =
    baseMeasure.withDensity (fun x => ENNReal.ofReal ((N.card : ℝ)⁻¹ *
      ∑ n ∈ N, ∏ i ∈ D, testedCoordinateWeight false I h α i (E i) (F i)
        (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i)))) := by
  simpa only [orbitTestWeight_eq_first_product] using
    TailTrimming.orbitAverageMeasure_restrict_first_marginal_real θ N
      (orbitWeight D I h α θ) (fun n _ => measurable_orbitWeight D I h α θ n)
      (fun n _ x => (orbitWeight_bounds D I hh hα θ n x).1)
      (rectangle D E F) (measurableSet_rectangle D E F hE hF)

theorem tested_second_marginal (D I N : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (θ : ℕ → ℝ) (E F : ℕ → Set ℝ)
    (hE : ∀ i ∈ D, MeasurableSet (E i)) (hF : ∀ i ∈ D, MeasurableSet (F i)) :
    ((TailTrimming.orbitAverageMeasure θ N
      (fun n x => ENNReal.ofReal (orbitWeight D I h α θ n x))).restrict
        (rectangle D E F)).map Prod.snd =
    baseMeasure.withDensity (fun y => ENNReal.ofReal ((N.card : ℝ)⁻¹ *
      ∑ n ∈ N, ∏ i ∈ D, testedCoordinateWeight true I h α i (E i) (F i)
        (circleRepresentative (y i)) (Int.fract ((n : ℝ) * θ i)))) := by
  simpa only [orbitTestWeight_eq_second_product] using
    TailTrimming.orbitAverageMeasure_restrict_second_marginal_real θ N
      (orbitWeight D I h α θ) (fun n _ => measurable_orbitWeight D I h α θ n)
      (fun n _ x => (orbitWeight_bounds D I hh hα θ n x).1)
      (rectangle D E F) (measurableSet_rectangle D E F hE hF)

end Invariant233.ProductModel.SamplingWeights

end

end OAI
