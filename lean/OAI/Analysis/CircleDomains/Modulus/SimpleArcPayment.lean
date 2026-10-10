import OAI.Analysis.CircleDomains.Probability.SimplePhysicalArcOccupation
import OAI.Analysis.CircleDomains.Probability.LevelPaymentMeasure
import OAI.Analysis.CircleDomains.Modulus.InterleavedCollarCost

namespace OAI

/-! Actual physical costs of a simple tagged arc are paid by the weighted
length and atomic boundary measure on the fixed prior level set. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem simple_arc_cost_le_levelPaymentMeasure
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (π : Y → X) (hπ : Measurable π)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H : Set X} (hH : MeasurableSet H) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) (hinj : Injective γ.val)
    {S : Set X} (hS : MeasurableSet S) (hγS : range γ.val ⊆ S)
    (hγH : range γ.val ⊆ H) :
    physicalTollCost d g m γ ≤ levelPaymentMeasure π d.physicalDomain H g m S := by
  have himage : (physicalValue d.domainEquiv d.basePoint ∘ γ.val) ''
      (γ.val ⁻¹' d.quotientDomain) ⊆ π ⁻¹' S ∩ (d.physicalDomain ∩ π ⁻¹' H) := by
    rintro y ⟨t, ht, rfl⟩
    change γ.val t ∈ d.quotientDomain at ht
    simp only [Function.comp_apply, physicalValue, dite_eq_left ht]
    have hproj : π (d.domainEquiv.symm ⟨γ.val t, ht⟩).val = γ.val t := by
      rw [he]
      exact congrArg Subtype.val (d.domainEquiv.apply_symm_apply ⟨γ.val t, ht⟩)
    refine ⟨?_, (d.domainEquiv.symm ⟨γ.val t, ht⟩).property, ?_⟩
    · change π (d.domainEquiv.symm ⟨γ.val t, ht⟩).val ∈ S
      rw [hproj]
      exact hγS (mem_range_self t)
    · change π (d.domainEquiv.symm ⟨γ.val t, ht⟩).val ∈ H
      rw [hproj]
      exact hγH (mem_range_self t)
  have hphysical : (∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint γ) ≤
      (((μH[1] : Measure Y).restrict (d.physicalDomain ∩ π ⁻¹' H)).withDensity g).map π S := by
    rw [Measure.map_apply hπ hS, withDensity_apply _ (hS.preimage hπ),
      Measure.restrict_restrict (hS.preimage hπ)]
    exact (simple_arc_physical_integral_le d.domainEquiv hU d.basePoint γ hinj g).trans
      (lintegral_mono' (Measure.restrict_mono himage le_rfl) le_rfl)
  have hatomic : boundaryToll γ.val m ≤ (atomicBoundaryMeasure m).restrict H S := by
    rw [Measure.restrict_apply hS]
    exact simple_arc_boundary_toll_le γ.val hinj m (hS.inter hH)
      (fun x hx => ⟨hγS hx, hγH hx⟩)
  rw [physicalTollCost, levelPaymentMeasure, Measure.add_apply]
  exact add_le_add hphysical hatomic

theorem simple_arc_cost_le_own_range
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (π : Y → X) (hπ : Measurable π)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H : Set X} (hH : MeasurableSet H) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) (hinj : Injective γ.val)
    (hγH : range γ.val ⊆ H) :
    physicalTollCost d g m γ ≤ levelPaymentMeasure π d.physicalDomain H g m (range γ.val) := by
  have hmeas : MeasurableSet (range γ.val) :=
    (isCompact_range γ.val.continuous).isClosed.measurableSet
  exact simple_arc_cost_le_levelPaymentMeasure d hU π hπ he (H := H) hH g m γ hinj
    (S := range γ.val) hmeas (fun _ hx => hx) hγH

end CircleDomainRigidity

end

end OAI
