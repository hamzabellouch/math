import OAI.Analysis.IrrationalRotation.Model.CircleSmoothing
import OAI.Analysis.IrrationalRotation.Analysis.SawtoothSmoothing
import OAI.Analysis.IrrationalRotation.Rotation.CircleRepresentative
import OAI.Analysis.IrrationalRotation.Sampling.CircleCharacterDynamics
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace OAI

namespace InvariantProjection.Continuity

open MeasureTheory Set
local notation "Circle" => AddCircle (1 : ℝ)
local notation "rep" => (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 x : ℝ))

theorem periodic_apply_fract {f : ℝ → ℝ} (hf : Function.Periodic f 1) (u : ℝ) :
    f (Int.fract u) = f u := by
  simpa only [Int.fract, zsmul_eq_mul, mul_one] using hf.sub_zsmul_eq (x := u) ⌊u⌋

@[simp] theorem circleSmoothSawtooth_coe (δ u : ℝ) :
    circleSmoothSawtooth δ (u : Circle) = smoothSawtooth δ u := by
  change smoothSawtooth δ (rep (u : Circle)) = smoothSawtooth δ u
  rw [Invariant233.CircleCharacterDynamics.representative_coe]
  exact periodic_apply_fract (smoothSawtooth_periodic δ) u

theorem continuous_circleSmoothSawtooth (δ : ℝ) :
    Continuous (circleSmoothSawtooth δ) := by
  apply AddCircle.liftIco_zero_continuous
  · simpa only [zero_add] using (smoothSawtooth_periodic δ 0).symm
  · exact (continuous_smoothSawtooth δ).continuousOn

@[simp] theorem circleSmoothedDrop_coe (C a δ u : ℝ) :
    circleSmoothedDrop C a δ (u : Circle) = smoothedDrop C a δ u := by
  unfold circleSmoothedDrop smoothedDrop
  simp only [← AddCircle.coe_add, circleSmoothSawtooth_coe]

theorem circleSmoothedDrop_eq_representative (C a δ : ℝ) (x : Circle) :
    circleSmoothedDrop C a δ x = smoothedDrop C a δ (rep x) := by
  rw [← circleSmoothedDrop_coe]
  exact congrArg (circleSmoothedDrop C a δ) AddCircle.coe_equivIco.symm

theorem circleSmoothingTransfer_eq_representative (C δ : ℝ) (x : Circle) :
    circleSmoothingTransfer C δ x = smoothingTransfer C δ (rep x) := by
  unfold circleSmoothingTransfer smoothingTransfer
  have hs : circleSmoothSawtooth δ x = smoothSawtooth δ (rep x) := by
    rw [← circleSmoothSawtooth_coe]
    exact congrArg (circleSmoothSawtooth δ) AddCircle.coe_equivIco.symm
  rw [hs]
  have hr : Int.fract (rep x) = rep x :=
    Int.fract_eq_self.mpr (by simpa using (AddCircle.equivIco 1 0 x).property)
  rw [hr]

theorem circleSmoothedDrop_eq_add_coboundary (C a δ : ℝ) (x : Circle) :
    circleSmoothedDrop C a δ x = C * (⌊rep x + a⌋ : ℝ) +
      circleSmoothingTransfer C δ x -
        circleSmoothingTransfer C δ (x + (a : Circle)) := by
  unfold circleSmoothedDrop circleSmoothingTransfer
  have hf : (⌊rep x + a⌋ : ℝ) = a + rep x - rep (x + (a : Circle)) := by
    rw [Invariant233.CircleCharacterDynamics.representative_add_real]
    have ht := Int.floor_add_fract (rep x + a)
    linarith
  rw [hf]
  ring

theorem continuous_circleSmoothedDrop (C a δ : ℝ) :
    Continuous (circleSmoothedDrop C a δ) := by
  unfold circleSmoothedDrop
  exact continuous_const.mul
    ((continuous_const.add (continuous_circleSmoothSawtooth δ)).sub
      ((continuous_circleSmoothSawtooth δ).comp (continuous_id.add_const (a : Circle))))

theorem measurable_circleSmoothingTransfer (C δ : ℝ) :
    Measurable (circleSmoothingTransfer C δ) := by
  unfold circleSmoothingTransfer
  exact measurable_const.mul ((continuous_circleSmoothSawtooth δ).measurable.sub
    Invariant233.CocycleSupport.measurePreserving_circleRepresentative.measurable)

theorem circleSmoothedDrop_nonneg {C a δ : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hδ : 0 < δ) (x : Circle) : 0 ≤ circleSmoothedDrop C a δ x := by
  rw [circleSmoothedDrop_eq_representative]
  exact smoothedDrop_nonneg hC ha hδ _

theorem integral_circleSmoothedDrop (C a δ : ℝ) :
    (∫ x : Circle, circleSmoothedDrop C a δ x) = C * a := by
  rw [← UnitAddCircle.intervalIntegral_preimage 0]
  simp only [circleSmoothedDrop_coe]
  simpa only [zero_add] using integral_smoothedDrop C a δ

theorem measure_circleSmoothingTransfer_support_le {δ : ℝ} (C : ℝ)
    (hδ : 0 < δ) :
    volume (Function.support (circleSmoothingTransfer C δ)) ≤ ENNReal.ofReal (2 * δ) := by
  have hm : Measurable (smoothingTransfer C δ) := by
    unfold smoothingTransfer
    exact measurable_const.mul ((continuous_smoothSawtooth δ).measurable.sub measurable_fract)
  have hs : MeasurableSet (Function.support (smoothingTransfer C δ)) := measurableSet_support hm
  have he := Invariant233.CocycleSupport.measurePreserving_circleRepresentative.measure_preimage
    hs.nullMeasurableSet
  rw [Measure.restrict_apply hs] at he
  have hsupp : Function.support (circleSmoothingTransfer C δ) =
      rep ⁻¹' Function.support (smoothingTransfer C δ) := by
    ext x
    simp only [Function.mem_support, Set.mem_preimage, circleSmoothingTransfer_eq_representative]
  rw [hsupp, he]
  convert measure_smoothingTransfer_support_le C hδ using 1
  congr 1
  ext u
  simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_ofPred_eq, and_comm]

theorem measure_circleSmoothedDrop_support_le {a δ : ℝ} (C : ℝ)
    (ha : 0 ≤ a) (hδ : 0 < δ) :
    volume (Function.support (circleSmoothedDrop C a δ)) ≤
      ENNReal.ofReal (a + 2 * δ) := by
  have hs : MeasurableSet (Function.support (smoothedDrop C a δ)) :=
    measurableSet_support (continuous_smoothedDrop C a δ).measurable
  have he := Invariant233.CocycleSupport.measurePreserving_circleRepresentative.measure_preimage
    hs.nullMeasurableSet
  rw [Measure.restrict_apply hs] at he
  have hsupp : Function.support (circleSmoothedDrop C a δ) =
      rep ⁻¹' Function.support (smoothedDrop C a δ) := by
    ext x
    simp only [Function.mem_support, Set.mem_preimage, circleSmoothedDrop_eq_representative]
  rw [hsupp, he]
  convert measure_smoothedDrop_support_le C ha hδ using 1
  congr 1
  ext u
  simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_ofPred_eq, and_comm]

theorem continuous_characterSmoothedDrop (C a δ : ℝ) (q : ℤ) :
    Continuous (fun x : Circle => circleSmoothedDrop C a δ (q • x)) :=
  (continuous_circleSmoothedDrop C a δ).comp (continuous_id.zsmul q)

theorem integral_characterSmoothedDrop (C a δ : ℝ) {q : ℤ} (hq : q ≠ 0) :
    (∫ x : Circle, circleSmoothedDrop C a δ (q • x)) = C * a := by
  have hp := Measure.measurePreserving_zsmul (volume : Measure Circle) hq
  have hm : AEStronglyMeasurable (circleSmoothedDrop C a δ)
      (Measure.map (fun x : Circle => q • x) volume) := by
    rw [hp.map_eq]
    exact (continuous_circleSmoothedDrop C a δ).aestronglyMeasurable
  have he := integral_map hp.measurable.aemeasurable hm
  rw [hp.map_eq] at he
  exact he.symm.trans (integral_circleSmoothedDrop C a δ)

theorem measure_characterSmoothedDrop_support_le {a δ : ℝ} (C : ℝ)
    (ha : 0 ≤ a) (hδ : 0 < δ) {q : ℤ} (hq : q ≠ 0) :
    volume (Function.support (fun x : Circle => circleSmoothedDrop C a δ (q • x))) ≤
      ENNReal.ofReal (a + 2 * δ) := by
  have hp := Measure.measurePreserving_zsmul (volume : Measure Circle) hq
  have hs := measurableSet_support (continuous_circleSmoothedDrop C a δ).measurable
  change volume ((fun x : Circle => q • x) ⁻¹' Function.support (circleSmoothedDrop C a δ)) ≤ _
  rw [hp.measure_preimage hs.nullMeasurableSet]
  exact measure_circleSmoothedDrop_support_le C ha hδ

theorem measure_characterSmoothingTransfer_support_le {δ : ℝ} (C : ℝ)
    (hδ : 0 < δ) {q : ℤ} (hq : q ≠ 0) :
    volume (Function.support (fun x : Circle => circleSmoothingTransfer C δ (q • x))) ≤
      ENNReal.ofReal (2 * δ) := by
  have hp := Measure.measurePreserving_zsmul (volume : Measure Circle) hq
  have hm : Measurable (circleSmoothingTransfer C δ) := by
    unfold circleSmoothingTransfer
    exact measurable_const.mul ((continuous_circleSmoothSawtooth δ).measurable.sub
      Invariant233.CocycleSupport.measurePreserving_circleRepresentative.measurable)
  change volume ((fun x : Circle => q • x) ⁻¹' Function.support (circleSmoothingTransfer C δ)) ≤ _
  rw [hp.measure_preimage (measurableSet_support hm).nullMeasurableSet]
  exact measure_circleSmoothingTransfer_support_le C hδ

theorem characterSmoothedDrop_eq_add_coboundary (C θ δ : ℝ) (q : ℤ) (x : Circle) :
    circleSmoothedDrop C (Int.fract ((q : ℝ) * θ)) δ (q • x) =
      C * (⌊rep (q • x) + Int.fract ((q : ℝ) * θ)⌋ : ℝ) +
      circleSmoothingTransfer C δ (q • x) -
      circleSmoothingTransfer C δ (q • (x + (θ : Circle))) := by
  rw [zsmul_add, Invariant233.CircleCharacterDynamics.zsmul_real_phase]
  exact circleSmoothedDrop_eq_add_coboundary C (Int.fract ((q : ℝ) * θ)) δ (q • x)

end InvariantProjection.Continuity

end OAI
