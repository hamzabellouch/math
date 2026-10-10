import OAI.Analysis.CircleDomains.Selection.CoordinateMapExclusion
import OAI.Analysis.CircleDomains.Sobolev.CircleIntegralCongruence

namespace OAI

/-! A strict lower bound for the constructed mean excludes the same
map--disk pair after passing to its measurable physical coordinate. -/

open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateData.circleFormIntegral_eq_of_physical_values
    {T : Type*} {G U S : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    (C : MaskedCoordinateData G U π σ) (hG : IsOpen G) (hS : IsOpen S) (hπ : Continuous π)
    (u : ℂ → UnitAddCircle)
    (hu : SmoothCircleOn u (((↑) : ℂ → Sphere) ⁻¹' G ∩
      (fun z : ℂ => π (z : Sphere)) ⁻¹' S))
    (hvalue : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
      C.physical (Complex.equivRealProdCLM z) = u z)
    (φ : ℂ → ℝ) {γ : ℝ → ℂ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ)
    (hγG : ∀ t, (γ t : Sphere) ∈ G) (hγS : ∀ t, π (γ t : Sphere) ∈ S)
    (hγM : ∀ t, Complex.equivRealProdCLM (γ t) ∈ interior (physicalMask π C.mask)) :
    circleFormIntegral φ (C.physical ∘ Complex.equivRealProdCLM) γ =
      circleFormIntegral φ u γ := by
  let O := Complex.equivRealProdCLM ⁻¹'
    (realChartDomain G ∩ interior (physicalMask π C.mask))
  have hO : IsOpen O := ((isOpen_realChartDomain hG).inter isOpen_interior).preimage
    Complex.equivRealProdCLM.continuous
  have hP : IsOpen (((↑) : ℂ → Sphere) ⁻¹' G ∩
      (fun z : ℂ => π (z : Sphere)) ⁻¹' S) :=
    (hG.preimage OnePoint.continuous_coe).inter
      (hS.preimage (hπ.comp OnePoint.continuous_coe))
  apply circleFormIntegral_eq_of_eq_on_curve hO hP _ hu φ hγ _
    (fun t => ⟨hγG t, hγS t⟩) (fun t => hvalue _ (hγG t) (hγS t))
  · intro z hz a ha
    exact (C.smooth _ hz a ha).comp z Complex.equivRealProdCLM.contDiff.contDiffAt
  · intro t
    refine ⟨?_, hγM t⟩
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈ G
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hγG t

 theorem MaskedCoordinateData.exists_mapDisk_exclusion_of_mean
    {T : Type*} {G U S : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    (C : MaskedCoordinateData G U π σ) (hG : IsOpen G) (hS : IsOpen S) (hπ : Continuous π)
    (u : ℂ → UnitAddCircle)
    (hu : SmoothCircleOn u (((↑) : ℂ → Sphere) ⁻¹' G ∩
      (fun z : ℂ => π (z : Sphere)) ⁻¹' S))
    (hvalue : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
      C.physical (Complex.equivRealProdCLM z) = u z)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π C.mask))
    (hγS : ∀ t, π (γ t : Sphere) ∈ S)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (c : ℂ) (r : ℝ≥0) (R : ℝ) (a : ℝ)
    (hbudget : C.sourceStokesBudget R ≤ a)
    (hlower : a < |circleFormIntegral
      (fun z => Metric.infDist (F z) (Metric.closedBall c (r : ℝ))) u γ|) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      (∀ t, (v t : UnitAddCircle) = C.physical (Complex.equivRealProdCLM (γ t))) ∧
      IsOpen (mapDiskExclusion
        (sourceCircuit γ hγ.smooth.continuous (fun t => hbd (mem_image_of_mem _ (hγ.mem_frontier t))))
        v (C.sourceStokesBudget R)) ∧
      (finiteSourceMap F hF, c, r) ∈ mapDiskExclusion
        (sourceCircuit γ hγ.smooth.continuous (fun t => hbd (mem_image_of_mem _ (hγ.mem_frontier t))))
        v (C.sourceStokesBudget R) := by
  apply C.exists_mapDisk_exclusion hG H γ hγ hbd hmask F hF c r R
  rw [C.circleFormIntegral_eq_of_physical_values hG hS hπ u hu hvalue _ hγ.smooth
    (fun t => hbd (mem_image_of_mem _ (hγ.mem_frontier t))) hγS]
  · exact hbudget.trans_lt hlower
  · intro t
    apply hmask
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈
      closedTerminalCap H
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact mem_image_of_mem _ (frontier_subset_closure (hγ.mem_frontier t))

end CircleDomainRigidity.FiniteTransfer

end

end OAI
