import OAI.Analysis.CircleDomains.Topology.SimpleArcToll
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OAI

/-! The measure used for the free-trace argument is constructed from
physical weighted length and actual boundary atoms on the prior level set. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

def levelPaymentMeasure {X Y : Type*} [MeasurableSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (π : Y → X) (G : Set Y) (H : Set X) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) : Measure X :=
  (((μH[1] : Measure Y).restrict (G ∩ π ⁻¹' H)).withDensity g).map π +
    (atomicBoundaryMeasure m).restrict H

theorem levelPaymentMeasure_finite {X Y : Type*}
    [MeasurableSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (π : Y → X) (hπ : Measurable π) (G : Set Y) (H : Set X)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hg : (∫⁻y in G ∩ π ⁻¹' H, g y ∂(μH[1] : Measure Y)) < ∞)
    (hm : atomicBoundaryMeasure m H < ∞) :
    IsFiniteMeasure (levelPaymentMeasure π G H g m) := by
  constructor
  rw [levelPaymentMeasure, Measure.add_apply, Measure.map_apply hπ MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_apply_univ, setLIntegral_univ]
  exact ENNReal.add_lt_top.mpr ⟨hg, hm⟩

theorem levelPaymentMeasure_free_null {X Y : Type*}
    [MeasurableSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (π : Y → X) (hπ : Measurable π) {G : Set Y} {U B H F : Set X}
    (hF : MeasurableSet F)
    (hπG : MapsTo π G U) (hUB : Disjoint U B) (hFB : F ⊆ B)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (hm : ∀x ∈ F, m x = 0) :
    levelPaymentMeasure π G H g m F = 0 := by
  have he : π ⁻¹' F ∩ (G ∩ π ⁻¹' H) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyF, hyG, _⟩
    exact Set.disjoint_left.mp hUB (hπG hyG) (hFB hyF)
  have hphysical : (((μH[1] : Measure Y).restrict (G ∩ π ⁻¹' H)).withDensity g).map π F = 0 := by
    rw [Measure.map_apply hπ hF, withDensity_apply _ (hF.preimage hπ),
      Measure.restrict_restrict (hF.preimage hπ), he, Measure.restrict_empty, lintegral_zero_measure]
  have hatomic : (atomicBoundaryMeasure m).restrict H F = 0 := by
    apply le_antisymm ?_ bot_le
    calc
      _ ≤ atomicBoundaryMeasure m F := Measure.restrict_apply_le _ _
      _ = 0 := atomicBoundaryMeasure_null m hF hm
  rw [levelPaymentMeasure, Measure.add_apply, hphysical, hatomic, zero_add]

end CircleDomainRigidity

end

end OAI
