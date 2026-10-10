import OAI.Analysis.CircleDomains.Uniformization.MixedAssignedLimit
import OAI.Analysis.CircleDomains.Topology.MixedCollarStokes

namespace OAI

/-! Every assigned mixed normal limit satisfies the actual fixed-source
collar exclusion. The terminal containment is derived from the shrinking
neighborhoods and the closed component quotient. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MixedModelExhaustion.eventually_marked_cap_in_open
    {S C : Type*} [LinearOrder C] {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C} {ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained (markedNeighborhoods σ) modelError ρ)
    (hclosed : IsClosedMap π) (s : S) {A : Set Sphere} (hA : IsOpen A)
    (hfiber : π ⁻¹' {σ s} ⊆ A) :
    ∀ᶠ n in atTop, closedTerminalCap ((M.stages n).terminals.H (M.markIndex n s)) ⊆ A := by
  let W := (π '' Aᶜ)ᶜ
  have hW : IsOpen W := (hclosed _ hA.isClosed_compl).isOpen_compl
  have hs : σ s ∈ W := by
    rintro ⟨p, hp, he⟩
    exact hp (hfiber he)
  have hpre : π ⁻¹' W ⊆ A := by
    intro p hp
    by_contra hn
    exact hp (mem_image_of_mem _ hn)
  exact (M.eventually_marked_cap_in_nhds s (hW.mem_nhds hs)).mono fun _ hn => hn.trans hpre

 theorem AssignedMixedModelLimit.continuousOn
    {S C : Type*} [LinearOrder C] {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
    {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    {M : MixedModelExhaustion d data retained O ε ρ}
    (L : AssignedMixedModelLimit M) : ContinuousOn L.function (((↑) : ℂ → Sphere) ⁻¹' G) := by
  intro z hz
  have h := continuousAt_finite_part_of_conformalAt (L.conformal.1 _ hz)
    (by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
  simpa only [extendAtInfinity_coe, finiteCoord_coe] using h.continuousWithinAt

 def MaskedCoordinateData.sourceStokesBudget
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : MaskedCoordinateData G U π σ) (R : ℝ) : ℝ :=
  Real.sqrt Real.pi * R * Real.sqrt
    (∫ x in realChartDomain G ∩ physicalMask π C.mask,
      fieldEnergy (circleGradient C.physical) (fun x => sphericalMetricFactor x • 1) x) +
  2 * Real.pi * R * Real.sqrt
    (∑' t : {t : S // t ≠ C.singular}, (C.upper t - C.lower t) ^ 2)

 theorem AssignedMixedModelLimit.excludes_source_collar
    (hgreen : UnorientedFiniteCircleGreenFormula) (hsch : PlanarSchoenflies)
    (harea : ExteriorCoefficientAreaTheorem)
    {S C : Type*} [LinearOrder C] {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C} {ρ : ℕ → ℝ}
    {M : MixedModelExhaustion d data retained (markedNeighborhoods σ) modelError ρ}
    (L : AssignedMixedModelLimit M)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (hπ : Continuous π) (hclosed : IsClosedMap π)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hH : ∀ z ∈ frontier (jordanInterior H), ‖z‖ ≤ 4 * M.real.radius)
    (j : C)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π (data j).mask))
    (hfiber : π ⁻¹' {σ (data j).singular} ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H)
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hp : ∀ t, (v t : UnitAddCircle) = (data j).physical (Complex.equivRealProdCLM (γ t))) :
    (boundaryCurveTrace (L.function ∘ γ) (L.continuousOn.comp_continuous hγ.smooth.continuous
      (fun t => hbd (mem_image_of_mem _ (hγ.mem_frontier t)))), L.center (data j).singular,
        (⟨L.radius (data j).singular, (L.bounds _).2.1⟩ : ℝ≥0)) ∉
      boundaryExclusionSet v ((data j).sourceStokesBudget (5 * M.real.radius)) := by
  have hm : ∀ z ∈ frontier (jordanInterior H), Complex.equivRealProdCLM z ∈
      interior (physicalMask π (data j).mask) := by
    intro z hz
    apply hmask
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈
      closedTerminalCap H
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact mem_image_of_mem _ (frontier_subset_closure hz)
  have hcap := M.eventually_marked_cap_in_open hclosed (data j).singular
    (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)) hfiber
  have hb := M.eventually_source_collar_stokes hgreen hsch harea hG hinf hπ H γ hγ hbd hH j
    hmask L.assignment (fun n => M.markIndex n (data j).singular)
    (M.eventually_markIndex _) hcap L.subsequence L.strict.tendsto_atTop
    (fun n => L.disk_center n (data j).singular) (fun n => L.disk_radius n (data j).singular)
    (L.disk_eq _)
  exact M.excludes_source_stokes_limit H γ hγ hbd j hm v hv hp
    L.subsequence L.strict.tendsto_atTop L.function L.continuousOn L.converges
    (fun n => L.disk_center n (data j).singular) (L.center _) (L.center_tendsto _)
    (fun n => L.disk_radius n (data j).singular) ⟨L.radius _, (L.bounds _).2.1⟩
    (fun n => (L.disk_bounds n _).2.1) (L.radius_tendsto _) (5 * M.real.radius) _ _
    modelError_tendsto hb

 theorem AssignedMixedModelLimit.source_collar_integral_le
    (hgreen : UnorientedFiniteCircleGreenFormula) (hsch : PlanarSchoenflies)
    (harea : ExteriorCoefficientAreaTheorem)
    {S C : Type*} [LinearOrder C] {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C} {ρ : ℕ → ℝ}
    {M : MixedModelExhaustion d data retained (markedNeighborhoods σ) modelError ρ}
    (L : AssignedMixedModelLimit M)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (hπ : Continuous π) (hclosed : IsClosedMap π)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hH : ∀ z ∈ frontier (jordanInterior H), ‖z‖ ≤ 4 * M.real.radius)
    (j : C)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π (data j).mask))
    (hfiber : π ⁻¹' {σ (data j).singular} ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H)
    : |circleFormIntegral
        (fun z => infDist (L.function z) (closedBall (L.center (data j).singular) (L.radius (data j).singular)))
        ((data j).physical ∘ Complex.equivRealProdCLM) γ| ≤
      (data j).sourceStokesBudget (5 * M.real.radius) := by
  let W := Complex.equivRealProdCLM ⁻¹'
    (realChartDomain G ∩ interior (physicalMask π (data j).mask))
  have hW : IsOpen W := ((isOpen_realChartDomain hG).inter isOpen_interior).preimage
    Complex.equivRealProdCLM.continuous
  have hγW : ∀ t, γ t ∈ W := by
    intro t
    refine ⟨?_, ?_⟩
    · change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈ G
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact hbd (mem_image_of_mem _ (hγ.mem_frontier t))
    · apply hmask
      change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈
        closedTerminalCap H
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact mem_image_of_mem _ (frontier_subset_closure (hγ.mem_frontier t))
  have hu : SmoothCircleOn ((data j).physical ∘ Complex.equivRealProdCLM) W := by
    intro z hz a ha
    exact ((data j).smooth _ hz a ha).comp z Complex.equivRealProdCLM.contDiff.contDiffAt
  obtain ⟨v, hv, hp⟩ := exists_smooth_real_circuit_lift hW hu hγ.smooth hγW
  have hex := L.excludes_source_collar hgreen hsch harea hG hinf hπ hclosed H γ hγ hbd hH j
    hmask hfiber v hv hp
  have hFW : ContinuousOn L.function W := L.continuousOn.mono (by
    intro z hz
    have hzG := hz.1
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ G at hzG
    rw [ContinuousLinearEquiv.symm_apply_apply] at hzG
    change (z : Sphere) ∈ G
    exact hzG)
  have he := circleFormIntegral_eq_boundaryPairFunctional hW hu hγ.smooth hγW L.function hFW
    (L.center (data j).singular) ⟨L.radius (data j).singular, (L.bounds _).2.1⟩ v hv.continuous hp
  change circleFormIntegral
    (fun z => infDist (L.function z) (closedBall (L.center (data j).singular) (L.radius (data j).singular)))
    ((data j).physical ∘ Complex.equivRealProdCLM) γ = _ at he
  rw [he]
  exact le_of_not_gt hex

end CircleDomainRigidity.FiniteTransfer

end

end OAI
