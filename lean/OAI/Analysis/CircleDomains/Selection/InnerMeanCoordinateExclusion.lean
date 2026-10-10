import OAI.Analysis.CircleDomains.Selection.SmallMeanCoordinateConstruction
import OAI.Analysis.CircleDomains.Rigidity.MaskIndependentMeanLowerBound
import OAI.Analysis.CircleDomains.Rigidity.InnerPeriodMask
import OAI.Analysis.CircleDomains.Topology.InnerCollarCoordinate
import OAI.Analysis.CircleDomains.Selection.MeanCircuitExclusion

namespace OAI

/-! Select the integration curve before its enclosing inner period mask.
The disk coordinate is used only inside its genuine outer Jordan disk. -/

open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem exists_gated_small_inner_mean_exclusion
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U S : Set Sphere} (e : G ≃ₜ U) (hG : IsOpen G) (hU : IsOpen U)
    (hdense : Dense U) (hS : IsOpen S)
    {T : Type*} (σ : T → Sphere) (hσ : ∀ s, σ s ∉ U) (singular : T)
    (hbS : σ singular ∉ S) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (he : ∀ y : G, (e y).val = π y.val)
    (hfreeU : π '' Gᶜ ⊆ Uᶜ) (hinf : π OnePoint.infty ∉ S)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map Subtype.val) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' G ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' S)))
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (hmiss : ∀ x ∈ U ∩ S, ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (hmissFree : ∀ x ∈ ((π '' Gᶜ) \ range σ) ∩ S,
      ∀ᵐ γ : K ∂(η.map f : Measure K), F x ∉ range γ.val)
    (hend : ∀ γ : A, σ singular ∈ range γ.val)
    (hbudget : Summable (fun s => ((η : Measure A).real {γ | σ s ∈ range γ.val}) ^ 2))
    (w : T → ℝ≥0∞) (hw : (∑' t, w t ^ 2) < ∞)
    (hwp : ∀ s, s ≠ singular → (η : Measure A) {γ | σ s ∈ range γ.val} ≤ w s)
    {R : ℝ} (hR : 0 ≤ R)
    {H J : ℂ ≃ₜ ℂ} (L : RegularJordanInwardCollar H)
    (hfront : frontier (((↑) : ℂ → Sphere) '' jordanInterior J) =
      π '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)))
    (hbJ : σ singular ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (hFJ : EqOn F (centeredJordanCoordinate J (σ singular))
      (closure (((↑) : ℂ → Sphere) '' jordanInterior J)))
    (D : OrderedCollarLift L (F.comp ⟨π, hπ⟩))
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) (σ singular))
    (havoid : ∀ x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior J),
      pathHitProbability (η.map Subtype.val) x = 0)
    (O : Set ℂ) (hO : IsOpen O) (hHO : frontier (jordanInterior H) ⊆ O)
    (hOG : ∀ z ∈ O, (z : Sphere) ∈ G)
    (hregion : π '' (((↑) : ℂ → Sphere) '' jordanInterior H) =
      ((↑) : ℂ → Sphere) '' jordanInterior J)
    (hJS : (((↑) : ℂ → Sphere) '' jordanInterior J) \ {σ singular} ⊆ S)
    (hstrict : ∀ x ∈ (((↑) : ℂ → Sphere) '' jordanInterior J) \ U, ‖F x‖ < 1)
    (F₀ : ℂ → ℂ) (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G))
    (hF₀m : Measurable F₀)
    (hF₀smooth : ContDiffOn ℝ (⊤ : ℕ∞) F₀ O)
    (c : ℂ) (r : ℝ≥0) (houtside : ∀ z ∈ O, (r : ℝ) < dist (F₀ z) c)
    {d₀ : ℝ} (hd₀ : 0 < d₀)
    (hgate : ∀ᵐ γ : A ∂(η : Measure A),
      d₀ ≤ Metric.infDist (F₀ (finiteCoord (physicalValue e y₀ (γ.val 0))))
        (Metric.closedBall c (r : ℝ)))
    (hsmall : (∫⁻ p, g p ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) + countingSquareNorm w <
      meanBudgetTolerance B R (d₀ / 4)) :
    ∃ (M : Set Sphere), IsClosed M ∧ frontier M ⊆ U ∧ σ singular ∈ M ∧
      π OnePoint.infty ∉ M ∧ M ⊆ ((↑) : ℂ → Sphere) '' jordanInterior J ∧
      ∃ (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F G U S M (σ singular) π)
      (C : MaskedCoordinateData G U π σ),
      C.graph = periodBandGraph U M (σ singular) Q.patch Q.branch ∧
      C.mask = M ∧ C.singular = singular ∧
      (∀ s, C.upper s - C.lower s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val}) ∧
      C.sourceStokesBudget R < d₀ / 4 ∧
      ∃ (ρ : ℝ) (v : ℝ → ℝ), ρ ∈ Ioc (0 : ℝ) D.width ∧
        realChartDomain (closedTerminalCap (L.disk ρ)) ⊆ interior (physicalMask π C.mask) ∧
        π ⁻¹' {σ singular} ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (L.disk ρ) ∧
        ContDiff ℝ (⊤ : ℕ∞) v ∧
        (∀ t, (v t : UnitAddCircle) = C.physical (Complex.equivRealProdCLM (L.curve ρ t))) ∧
        ∃ V : Set (MapDiskData G), IsOpen V ∧
          (finiteSourceMap F₀ hF₀, c, r) ∈ V ∧
          ∃ (γ : C(PathTime, FiniteSource G)),
            (∀ t, (γ t).val = L.curve ρ t) ∧ V = mapDiskExclusion γ v (C.sourceStokesBudget R) := by
  let Φ : ℂ → ℝ := fun z => Metric.infDist (F₀ z) (Metric.closedBall c (r : ℝ))
  have hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ O :=
    contDiffOn_distance_from_disk_comp hF₀smooth c r.property houtside
  have hΦm : Measurable Φ :=
    (Metric.continuous_infDist_pt (Metric.closedBall c (r : ℝ))).measurable.comp hF₀m
  obtain ⟨δ, hδ, hδ1, a, ha, haD, hlower⟩ := exists_gated_mean_collar_lower_bound_all_masks
    hsch hsep G U S e hG hU hS y₀ π hπ he
    (fun z hz => hOG z (hHO hz)) hfront hbJ F hFJ D A K η hAS hK hKS
    f hf hmap havoid O hO hHO Φ hΦm hΦ hd₀ hgate
  obtain ⟨b, hb, hbL, hnear⟩ := L.eventually_in_boundary_neighborhood hO hHO
  have htarget : σ singular ∈ π '' (((↑) : ℂ → Sphere) '' jordanInterior H) := by
    rw [hregion]
    exact hbJ
  obtain ⟨_, ⟨z, hz, rfl⟩, hzb⟩ := htarget
  obtain ⟨a₀, ha₀, ha₀w, hkeep⟩ := L.retains_compact {z} isCompact_singleton
    (singleton_subset_iff.mpr hz)
  let ρ := min a (min b a₀) / 2
  have hmin : 0 < min a (min b a₀) := lt_min ha (lt_min hb ha₀)
  have hρ : 0 < ρ := half_pos hmin
  have hhalf : ρ ≤ min a (min b a₀) := half_le_self hmin.le
  have hρa : ρ ≤ a := hhalf.trans (min_le_left _ _)
  have hρb : ρ ≤ b := hhalf.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρa₀ : ρ ≤ a₀ := hhalf.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hρD : ρ ∈ Ioc (0 : ℝ) D.width := ⟨hρ, hρa.trans haD.le⟩
  have hρL : ρ ∈ Icc (0 : ℝ) L.width := ⟨hρ.le, hρD.2.trans D.width_le⟩
  have hboundaryO : frontier (jordanInterior (L.disk ρ)) ⊆ O := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := (L.parametrization ρ hρL).boundary.symm ▸ hz
    exact hnear ρ ⟨hρ.le, hρb⟩ t ht
  have hinnerS : ∀ z ∈ frontier (jordanInterior (L.disk ρ)), π (z : Sphere) ∈ S := by
    intro z hz
    apply hJS
    exact D.inner_frontier_punctured hπ
      (by rw [hFJ (subset_closure hbJ), centeredJordanCoordinate_self])
      hregion hρ (hρa.trans_lt haD) z hz
  have hcurve (t : ℝ) : (D.circuit ρ t : Sphere) ∈ G ∧
      π (D.circuit ρ t : Sphere) ∈ S :=
    ⟨hOG _ (hboundaryO (D.circuit_mem_frontier hρL t)),
      hinnerS _ (D.circuit_mem_frontier hρL t)⟩
  have havoidK (t : ℝ) : ∀ᵐ α : K ∂(η.map f : Measure K),
      F (π (D.circuit ρ t : Sphere)) ∉ range α.val := by
    apply mapped_arc_point_avoidance A K η F f hf hmap
    · intro γ
      exact (hF γ).mono (union_subset_union Subset.rfl
        (singleton_subset_iff.mpr (hcurve t).2))
    · apply hmiss _ ⟨?_, (hcurve t).2⟩
      rw [← he ⟨_, (hcurve t).1⟩]
      exact (e ⟨_, (hcurve t).1⟩).property
  obtain ⟨M, hM, hboundary, hinfM, hMH, hcap⟩ := L.exists_inner_period_mask hG π hπ
    hclosed hsurj hr (fun z hz => (he ⟨_, hz⟩) ▸ (e ⟨_, hz⟩).property)
    (fun z hz => hOG z (hHO hz))
    (isCompact_closure_jordanInterior (L.disk ρ)) (L.inward ρ ⟨hρ, hρL.2⟩)
  have hMJ : M ⊆ ((↑) : ℂ → Sphere) '' jordanInterior J := by
    rw [← hregion]
    exact hMH
  have hbM : σ singular ∈ M := by
    have hzcap : z ∈ closure (jordanInterior (L.disk ρ)) :=
      subset_closure (hkeep ρ ⟨hρ, hρa₀⟩ (mem_singleton z))
    have hzmask := interior_subset (hcap (show Complex.equivRealProdCLM z ∈
        realChartDomain (((↑) : ℂ → Sphere) '' closure (jordanInterior (L.disk ρ))) from by
      exact ⟨z, hzcap, by
        exact congrArg ((↑) : ℂ → Sphere) (Complex.equivRealProdCLM.symm_apply_apply z).symm⟩))
    change π ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ M at hzmask
    simpa only [ContinuousLinearEquiv.symm_apply_apply, hzb] using hzmask
  have hMS : M \ {σ singular} ⊆ S := fun x hx => hJS ⟨hMJ hx.1, hx.2⟩
  have hstrictM : ∀ x ∈ M \ U, ‖F x‖ < 1 := fun x hx => hstrict x ⟨hMJ hx.1, hx.2⟩
  obtain ⟨Q, C, herr, hgraph, hmask, hsing, hwidth, hvalue, hbudget⟩ :=
    exists_smooth_mean_coordinate_with_small_budget hsch hsep hcoarea e hG hU hdense
      hS hM hboundary σ hσ singular hbS hMS y₀ π hπ he hfreeU hinf A hA η hfinite
      g hg hocc henergy K hK hKS F f hf hmap B hB h0 h1 hstrictM hF hinj hmiss hmissFree
      hend hbudget w hw hwp hR δ hδ hδ1 (by positivity : 0 < d₀ / 4) hsmall
  have herror : ∀ x, |Q.error x| ≤ δ := fun x =>
    (herr x).trans ((dustSmoothingTolerance_le_half id Uᶜ δ x).trans (by linarith))
  have hlow := hlower ρ ⟨hρ, hρa⟩ M Q herror hcurve havoidK
  have hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (L.disk ρ)) ⊆ G := by
    rintro _ ⟨z, hz, rfl⟩
    exact hOG z (hboundaryO hz)
  have hmask' : realChartDomain (closedTerminalCap (L.disk ρ)) ⊆
      interior (physicalMask π C.mask) := by rw [hmask]; exact hcap
  have hfiber : π ⁻¹' {σ singular} ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (L.disk ρ) := by
    have hsat := preimage_image_jordanInterior_of_component_collapse G π hsurj hr
      (L.disk ρ) (fun z hz => hbd (mem_image_of_mem _ hz))
    intro p hp
    rw [← hsat]
    exact ⟨(z : Sphere), ⟨z, hkeep ρ ⟨hρ, hρa₀⟩ (mem_singleton z), rfl⟩,
      hzb.trans (mem_singleton_iff.mp hp).symm⟩
  obtain ⟨v, hv, hproj, hV, hmem⟩ := C.exists_mapDisk_exclusion_of_mean hG hS hπ
    Q.physical Q.physical_smooth hvalue (L.disk ρ) (L.curve ρ) (L.parametrization ρ hρL)
    hbd hmask' (fun t => hinnerS _ ((L.parametrization ρ hρL).mem_frontier t))
    F₀ hF₀ c r R (d₀ / 4) hbudget.le (by exact lt_trans (by linarith) hlow)
  let γ := sourceCircuit (L.curve ρ) (L.parametrization ρ hρL).smooth.continuous
    (fun t => hbd (mem_image_of_mem _ ((L.parametrization ρ hρL).mem_frontier t)))
  exact ⟨M, hM, hboundary, hbM, hinfM, hMJ, Q, C, hgraph, hmask, hsing, hwidth, hbudget, ρ, v, hρD, hmask', hfiber, hv, hproj,
    mapDiskExclusion γ v (C.sourceStokesBudget R), hV, hmem, γ, (fun _ => rfl), rfl⟩

end CircleDomainRigidity

end

end OAI
