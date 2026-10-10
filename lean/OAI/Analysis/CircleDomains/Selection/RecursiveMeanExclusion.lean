import OAI.Analysis.CircleDomains.Selection.InnerMeanCoordinateExclusion
import OAI.Analysis.CircleDomains.Probability.CenteredTerminalLaw
import OAI.Analysis.CircleDomains.Selection.RecursiveReductionBase
import OAI.Analysis.CircleDomains.Selection.MeanExclusionWitness

namespace OAI

/-! The actual compact recursive positive law constructs an inner masked mean
and its open map--disk exclusion. Its energy and point-hit hypotheses are all
supplied by the law; only the geometric collar and prescribed gate are inputs. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal Classical
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

structure RecursiveMeanOutput (hsch : PlanarSchoenflies)
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    {L : RecursiveCodeLaw base π Flags ω} {J : ℂ ≃ₜ ℂ} {ε : ℝ≥0∞}
    (Q : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J) ε)
    (F₀ : ℂ → ℂ)
    (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain))
    (c : ℂ) (r : ℝ≥0) (R δ : ℝ) where
  centered : CenteredTerminalFamily J L.data.target Q.arcs
  mask : Set Sphere
  closed : IsClosed mask
  frontier : frontier mask ⊆ base.quotientDomain
  target_mem : L.data.target ∈ mask
  infty_not_mem : π OnePoint.infty ∉ mask
  inner : mask ⊆ ((↑) : ℂ → Sphere) '' jordanInterior J
  mean : SmoothMeanPeriodData hsch centered.diskArcs centered.terminal
    (Q.law.map centered.arcMap) centered.map base.physicalDomain base.quotientDomain
    centered.punctured mask L.data.target π
  coordinate : MaskedCoordinateData base.physicalDomain base.quotientDomain π
    (fun x : base.dust => x.val)
  graph : coordinate.graph = periodBandGraph base.quotientDomain mask L.data.target
    mean.patch mean.branch
  mask_eq : coordinate.mask = mask
  singular_eq : (coordinate.singular : Sphere) = L.data.target
  budget : coordinate.sourceStokesBudget R < δ
  exclusion : MeanExclusionWitness coordinate F₀ hF₀ c r R

 theorem CompactRecursiveReduction.exists_mean_exclusion
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    {L : RecursiveCodeLaw base π Flags ω}
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    {H J : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H)
    (hregion : π '' (((↑) : ℂ → Sphere) '' jordanInterior H) =
      ((↑) : ℂ → Sphere) '' jordanInterior J)
    (hbJ : L.data.target ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (hinfty : π OnePoint.infty ∉ closure (((↑) : ℂ → Sphere) '' jordanInterior J))
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹'
          ((((↑) : ℂ → Sphere) '' jordanInterior J) \ {L.data.target}))))
    {R : ℝ} (hR : 0 ≤ R) {d₀ : ℝ} (hd₀ : 0 < d₀)
    (Q : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J)
      (meanBudgetTolerance B R (d₀ / 4)))
    (O : Set ℂ) (hO : IsOpen O) (hHO : frontier (jordanInterior H) ⊆ O)
    (hOG : ∀ z ∈ O, (z : Sphere) ∈ base.physicalDomain)
    (F₀ : ℂ → ℂ)
    (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain))
    (hF₀m : Measurable F₀) (hF₀smooth : ContDiffOn ℝ (⊤ : ℕ∞) F₀ O)
    (c : ℂ) (r : ℝ≥0) (houtside : ∀ z ∈ O, (r : ℝ) < dist (F₀ z) c)
    (hgate : ∀ᵐ γ : Q.arcs ∂(Q.law : Measure Q.arcs),
      d₀ ≤ Metric.infDist (F₀ (finiteCoord (physicalValue base.domainEquiv base.basePoint (γ.val 0))))
        (Metric.closedBall c (r : ℝ))) :
    Nonempty (RecursiveMeanOutput hsch Q F₀ hF₀ c r R (d₀ / 4)) := by
  obtain ⟨P⟩ := exists_centered_terminal_family J hbJ Q.arcs Q.compact Q.terminal
  have hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ base.physicalDomain :=
    fun z hz => hOG z (hHO hz)
  have hfront := frontier_quotient_jordan_collar base.physicalDomain π hπ hclosed hsurj hr
    H J hboundary hregion
  obtain ⟨D⟩ := exists_quotient_ordered_collar_lift base.physicalDomain π hπ hclosed hsurj hr
    H J C hboundary hregion hbJ P.map P.map_eq
  let singular : base.dust := ⟨L.data.target, L.target_dust⟩
  have hσ : ∀ s : base.dust, s.val ∉ base.quotientDomain := by
    intro s
    exact (Set.ext_iff.mp hdust s.val).mp s.property
  have hmiss : ∀ x ∈ base.quotientDomain ∩ P.punctured,
      ∀ᵐ γ : Q.arcs ∂(Q.law : Measure Q.arcs), x ∉ range γ.val := by
    intro x hx
    apply Q.avoids_domain hU hG hdust hπ hclosed hsurj hr x hx.1
    intro hxi
    exact hinfty (hxi ▸ subset_closure hx.2.1)
  have havoid : ∀ x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior J),
      pathHitProbability (Q.law.map Subtype.val) x = 0 := by
    intro x hx
    have hxU : x ∈ base.quotientDomain := by
      rw [hfront] at hx
      obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hx
      rw [← he ⟨_, hboundary z hz⟩]
      exact (base.domainEquiv ⟨_, hboundary z hz⟩).property
    have hz := Q.avoids_domain hU hG hdust hπ hclosed hsurj hr x hxU
      (fun hxi => hinfty (hxi ▸ frontier_subset_closure hx))
    rw [Q.hit_probability]
    apply ae_iff.mp at hz
    simpa only [not_not] using hz
  have hmissFree : ∀ x ∈ ((π '' base.physicalDomainᶜ) \ range (fun s : base.dust => s.val)) ∩ P.punctured,
      ∀ᵐ γ : P.diskArcs ∂(Q.law.map P.arcMap : Measure P.diskArcs),
        P.map x ∉ range γ.val := by
    rintro x ⟨⟨⟨p, hp, rfl⟩, hx⟩, _⟩
    exact (hx ⟨⟨π p, hdust.symm ▸ hbad p hp⟩, rfl⟩).elim
  have hwp : ∀ s : base.dust, s ≠ singular →
      (Q.law : Measure Q.arcs) {γ | s.val ∈ range γ.val} ≤ Q.baseHitWeight s := by
    intro s hs
    apply Q.baseHitWeight_le s
    exact fun heq => hs (Subtype.ext heq)
  obtain ⟨M, hM, hbdM, hbM, hinfM, hMJ, u, N, hN, hNM, hNb, _, hbudget,
    ρ, v, hρ, hcap, hfiber, hv, hproj, V, _, hmem, γ, hγ, hV⟩ :=
    exists_gated_small_inner_mean_exclusion hsch hsep hcoarea base.domainEquiv hG hU hdense
      P.punctured_open (fun s : base.dust => s.val) hσ singular
      (by exact fun h => h.2 rfl) base.basePoint π hπ hclosed hsurj hr he
      (by rintro _ ⟨p, hp, rfl⟩; exact hbad p hp)
      (fun h => hinfty (subset_closure h.1)) Q.arcs (fun γ hγ => (Q.terminal hγ).1)
      Q.law (Q.base_finite_length he) Q.density Q.density_measurable (Q.base_occupation he)
      Q.density_energy_finite P.diskArcs P.compact P.terminal P.map P.arcMap
      P.continuous_arcMap.measurable P.arcMap_eq B hB (P.nonzero hbJ) (P.norm_le hbJ)
      (P.injective_arcs hbJ Q.terminal) (P.injective_punctured hbJ) hmiss hmissFree
      (CenteredTerminalFamily.endpoint Q.terminal) Q.base_hit_square_summable Q.baseHitWeight
      Q.baseHitWeight_square_finite hwp hR C hfront hbJ P.map_eq D Q.terminal havoid
      O hO hHO hOG hregion Subset.rfl (fun x hx => P.norm_lt hbJ x hx.1)
      F₀ hF₀ hF₀m hF₀smooth c r houtside hd₀ hgate Q.base_small
  have hρC : ρ ∈ Icc (0 : ℝ) C.width := ⟨hρ.1.le, hρ.2.trans D.width_le⟩
  have hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk ρ)) ⊆ base.physicalDomain := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (C.parametrization ρ hρC).boundary.symm ▸ hz
    have h := (γ ⟨t, ht⟩).property
    rwa [hγ] at h
  let γ₀ := sourceCircuit (C.curve ρ) (C.parametrization ρ hρC).smooth.continuous
    (fun t => hbd (mem_image_of_mem _ ((C.parametrization ρ hρC).mem_frontier t)))
  have hγeq : γ = γ₀ := by
    ext t
    exact hγ t
  have hexclusion : MeanExclusionWitness N F₀ hF₀ c r R := {
    disk := C.disk ρ
    curve := C.curve ρ
    regular := C.parametrization ρ hρC
    boundary := hbd
    mask := hcap
    fiber := by simpa only [hNb] using hfiber
    lift := v
    smooth_lift := hv
    projects := hproj
    member := by simpa only [hV, hγeq] using hmem }
  exact ⟨{
    centered := P, mask := M, closed := hM, frontier := hbdM, target_mem := hbM,
    infty_not_mem := hinfM, inner := hMJ, mean := u, coordinate := N, graph := hN,
    mask_eq := hNM, singular_eq := congrArg Subtype.val hNb, budget := hbudget,
    exclusion := hexclusion }⟩

end CircleDomainRigidity

end

end OAI
