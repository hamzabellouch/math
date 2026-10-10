import OAI.Analysis.IrrationalRotation.Rotation.FiniteSupportWeights
import OAI.Analysis.IrrationalRotation.Rotation.CircleRepresentative
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.CircleWeightSupport

theorem measurePreserving_characterRepresentative (q : ℤ) (hq : q ≠ 0) :
    MeasurePreserving
      (fun x : UnitAddCircle => ((AddCircle.equivIco (1 : ℝ) 0 (q • x)) : ℝ))
      volume (volume.restrict (Ico (0 : ℝ) 1)) := by
  exact CocycleSupport.measurePreserving_circleRepresentative.comp
    (Measure.measurePreserving_zsmul volume hq)

theorem ae_all_int_finite_floor_support {ι : Type*} [Countable ι]
    (q : ι → ℤ) (hq : ∀ i, q i ≠ 0)
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∀ᵐ x ∂(volume : Measure UnitAddCircle), ∀ k : ℤ,
      (Function.support (fun i =>
        Int.floor (((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ) +
          (k : ℝ) * α i))).Finite := by
  exact FiniteSupportWeights.ae_all_finite_floor_support volume
    (fun i x => ((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ))
    (fun i => measurePreserving_characterRepresentative (q i) (hq i)) α hα0 hα

theorem exists_invariant_conull_floor_support {ι : Type*} [Countable ι]
    (θ : ℝ) (q : ι → ℤ) (hq : ∀ i, q i ≠ 0)
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∃ s : Set UnitAddCircle, MeasurableSet s ∧ (∀ᵐ x ∂volume, x ∈ s) ∧
      (∀ (n : ℤ) x, x + n • (θ : UnitAddCircle) ∈ s ↔ x ∈ s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        (Function.support (fun i =>
          Int.floor (((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ) +
            (k : ℝ) * α i))).Finite := by
  apply FiniteSupportWeights.exists_invariant_conull_floor_support
    (volume : Measure UnitAddCircle) (fun n x => x + n • (θ : UnitAddCircle))
    (fun n => measurePreserving_add_right volume (n • (θ : UnitAddCircle)))
    (by intro x; simp)
    (by intro m n x; simp [add_zsmul, add_comm, add_left_comm])
    (fun i x => ((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ))
    (fun i => measurePreserving_characterRepresentative (q i) (hq i)) α hα0 hα

theorem measurable_exp_weight {ι : Type*} [Countable ι]
    (q : ι → ℤ) (hq : ∀ i, q i ≠ 0) (α c : ι → ℝ) :
    Measurable (fun x : UnitAddCircle => Real.exp (-(∑' i,
      c i * (Int.floor (((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ) + α i) : ℝ)))) := by
  apply Measurable.exp
  apply Measurable.neg
  apply Measurable.tsum
  intro i
  apply Measurable.mul measurable_const
  exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
    (((measurePreserving_characterRepresentative (q i) (hq i)).measurable.add_const _).floor)

theorem ae_summable_weighted_floors {ι : Type*} [Countable ι]
    (q : ι → ℤ) (hq : ∀ i, q i ≠ 0)
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) (c : ι → ℝ) :
    ∀ᵐ x ∂(volume : Measure UnitAddCircle),
      Summable (fun i => c i *
        (Int.floor (((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ) + α i) : ℝ)) := by
  filter_upwards [ae_all_int_finite_floor_support q hq α hα0 hα] with x hx
  apply FiniteSupportWeights.summable_mul_cost
  have hf : (Function.support (fun i =>
      Int.floor (((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ) + α i))).Finite := by
    simpa only [Int.cast_one, one_mul] using hx 1
  apply hf.subset
  intro i hi
  simp only [Function.mem_support] at hi ⊢
  intro h
  exact hi (by simp [h])

theorem exp_weight_mem_Ioc {ι : Type*} (q : ι → ℤ) (α c : ι → ℝ)
    (hα0 : ∀ i, 0 ≤ α i) (hc : ∀ i, 0 ≤ c i) (x : UnitAddCircle) :
    Real.exp (-(∑' i,
      c i * (Int.floor (((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ) + α i) : ℝ)))
       ∈ Set.Ioc (0 : ℝ) 1 := by
  apply FiniteSupportWeights.exp_neg_tsum_mem_Ioc c _ hc
  intro i
  apply Int.cast_nonneg
  apply Int.floor_nonneg.mpr
  exact add_nonneg (AddCircle.equivIco (1 : ℝ) 0 (q i • x)).property.1 (hα0 i)

end Invariant233.CircleWeightSupport

end OAI
