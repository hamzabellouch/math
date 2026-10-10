import OAI.Analysis.CircleDomains.Topology.AssignedCollarExclusion
import OAI.Analysis.CircleDomains.Sobolev.CircleGradientSize
import OAI.Analysis.CircleDomains.Modulus.BandBudgetNorm

namespace OAI

/-! Quantitative bounds for the actual source budget, on the same closed
mask and with the singular label omitted from the point-hit norm. -/

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateData.sourceStokesBudget_le
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : MaskedCoordinateData G U π σ) (hπ : Continuous π) {R : ℝ} (hR : 0 ≤ R)
    {A : ℝ≥0∞} (hA : A ≠ ∞)
    (hpartial : ∀ i : Fin 2, eLpNorm (fun x => circleFDeriv C.physical x
      (if i = 0 then (1, 0) else (0, 1))) 2
      (volume.restrict (realChartDomain G ∩ physicalMask π C.mask)) ≤ A)
    {T : Type*} (w : T → ℝ≥0∞) (e : {s : S // s ≠ C.singular} → T)
    (he : Function.Injective e)
    (hwidth : ∀ s : {s : S // s ≠ C.singular}, ENNReal.ofReal (C.upper s - C.lower s) ≤ w (e s))
    (hw : (∑' t, w t ^ 2) < ∞) :
    C.sourceStokesBudget R ≤
      2 * Real.sqrt Real.pi * R * A.toReal + 2 * Real.pi * R * (countingSquareNorm w).toReal := by
  have hmask : MeasurableSet (physicalMask π C.mask) := by
    exact ((C.mask_closed.preimage hπ).preimage
      (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)).measurableSet
  have henergy := C.energy
  rw [Measure.restrict_restrict hmask, inter_comm] at henergy
  have hx := ENNReal.toReal_mono hA (hpartial 0)
  have hy := ENNReal.toReal_mono hA (hpartial 1)
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero] at hx hy
  have hnorm := circle_gradient_norm_le_partial_norms henergy
  have hnorm' : Real.sqrt (∫ x in realChartDomain G ∩ physicalMask π C.mask,
      fieldEnergy (circleGradient C.physical) (fun z => sphericalMetricFactor z • 1) x) ≤
      2 * A.toReal := by linarith
  have hband := real_square_norm_le_counting
    (fun s : {s : S // s ≠ C.singular} => C.upper s - C.lower s) w e he
    (fun s => C.width_nonneg s) hwidth hw
  unfold sourceStokesBudget
  calc
    _ ≤ Real.sqrt Real.pi * R * (2 * A.toReal) +
        2 * Real.pi * R * (countingSquareNorm w).toReal := by gcongr
    _ = _ := by ring

end CircleDomainRigidity.FiniteTransfer

end

end OAI
