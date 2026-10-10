import OAI.Analysis.CircleDomains.Topology.SourceCollarStokes
import OAI.Analysis.CircleDomains.Topology.MixedCollarBound
import OAI.Analysis.CircleDomains.Uniformization.MixedStokesLimit

namespace OAI

/-! The actual finite Stokes bounds along a mixed exhaustion. The source
collar determines the holes; normalization supplies the common radius. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MixedModelExhaustion.eventually_source_collar_stokes
    (hgreen : UnorientedFiniteCircleGreenFormula) (hsch : PlanarSchoenflies)
    (harea : ExteriorCoefficientAreaTheorem)
    {S C : Type*} [LinearOrder C]
    {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
    {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained O ε ρ)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (hπ : Continuous π)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hH : ∀ z ∈ frontier (jordanInterior H), ‖z‖ ≤ 4 * M.real.radius)
    (j : C)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π (data j).mask))
    (a : ∀ n, TerminalComponentAssignment (M.stages n).terminals.H
      (M.stages n).model.forward (M.stages n).model.domain)
    (s : ∀ n, (M.stages n).indices)
    (hs : ∀ᶠ n in atTop, (s n : S) = (data j).singular)
    (hcap : ∀ᶠ n in atTop, closedTerminalCap ((M.stages n).terminals.H (s n)) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior H)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (c : ℕ → ℂ) (r : ℕ → ℝ)
    (hdisks : ∀ᶠ n in atTop,
      connectedComponentIn (M.stages (k n)).model.domainᶜ ((a (k n)).point (s (k n))) =
        ((↑) : ℂ → Sphere) '' closedBall (c n) (r n)) :
    ∀ᶠ n in atTop,
      |circleFormIntegral (fun z => infDist z (closedBall (c n) (r n)))
        (fun z => sphereRealFunction ((M.stages (k n)).model.functions (M.coordinateIndex j (k n)))
          ((M.stages (k n)).model.inverse (z : Sphere)))
        (fun t => finiteCoord ((M.stages (k n)).model.forward (γ t : Sphere)))| ≤
      Real.sqrt Real.pi * (5 * M.real.radius) * Real.sqrt
        ((∫ x in realChartDomain G ∩ physicalMask π (data j).mask,
          fieldEnergy (circleGradient (data j).physical) (fun x => sphericalMetricFactor x • 1) x) + ε (k n)) +
      2 * Real.pi * (5 * M.real.radius) * (Real.sqrt
        (∑' t : {t : S // t ≠ (data j).singular}, ((data j).upper t - (data j).lower t) ^ 2) + ε (k n)) := by
  have hK : IsCompact (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) :=
    ((isCompact_closure_jordanInterior H).of_isClosed_subset isClosed_frontier
      frontier_subset_closure).image OnePoint.continuous_coe
  filter_upwards [hk (M.eventually_all_image_collar_bounds harea H hbd hH),
    hk (M.coordinateIndex_eventually j), hk (M.real.eventually_core_contains hK hbd),
    hk hs, hk hcap, hdisks] with n hbounds hj hcore hsn hcn hdn
  change M.label (k n) (M.coordinateIndex j (k n)) = j at hj
  change (s (k n) : S) = (data j).singular at hsn
  have hretain : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆
      openCompletedRegion (M.stages (k n)).terminals.H := by
    rintro _ ⟨z, hz, rfl⟩
    apply (M.stages (k n)).core_model
    apply (coe_mem_sphericalCore _ _).mpr
    apply interior_subset ((M.stages (k n)).core_contains ?_)
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ M.real.cores (k n)
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hcore (mem_image_of_mem _ hz)
  have hi : OnePoint.infty ∈ (M.stages (k n)).model.domain := by
    rw [← (M.stages (k n)).model.principal.1]
    exact (M.stages (k n)).model.equivalence.mapsTo
      ((M.stages (k n)).core_model (infty_mem_sphericalCore (M.stages (k n)).core))
  obtain ⟨cn, rn, hrn, hends, hdn', hext⟩ :=
    (a (k n)).exists_disk_coordinates (M.stages (k n)).model.circle_domain hi
  have heq : closedBall (cn (s (k n))) (rn (s (k n))) = closedBall (c n) (r n) :=
    Set.image_injective.mpr OnePoint.coe_injective ((hends (s (k n))).symm.trans hdn)
  have hb := (M.stages (k n)).toMaskedCoordinateStage.source_collar_stokes_bound hgreen hsch
    hG hinf hπ d.labels_injective d.labels_dust (M.stages (k n)).real.metric_conformal
    (M.coordinateIndex j (k n)) (a (k n)) cn rn hrn hends hdn' hext H γ hγ.toRegular hretain
    (by simpa only [hj] using hmask) (s (k n)) (by simpa only [hj] using hsn) hcn
    (mul_nonneg (by norm_num) M.real.radius_pos.le)
    (fun J hJ => subset_closure.trans (hbounds J hJ))
  rw [hj] at hb
  simpa only [heq] using hb

end CircleDomainRigidity.FiniteTransfer

end

end OAI
