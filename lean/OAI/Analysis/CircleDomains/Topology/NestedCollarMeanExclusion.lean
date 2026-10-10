import OAI.Analysis.CircleDomains.Selection.RecursiveMeanExclusion
import OAI.Analysis.CircleDomains.Modulus.WeightedCollarTopology
import OAI.Analysis.CircleDomains.Topology.QuotientCollarJordan
import OAI.Analysis.CircleDomains.Topology.QuotientLocalChart
import OAI.Analysis.CircleDomains.Topology.RelativelyClosedGates

namespace OAI

/-! A single physical chart bound works throughout the nested collars. The
actual recursive law then supplies the small compact law at every sufficiently
deep collar, with the prescribed start gate and the resulting mean exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal Classical
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem RecursiveCodeLaw.eventually_gated_collar_mean
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea) (hcollar : SmoothRegularJordanCollars)
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    (L : RecursiveCodeLaw base π Flags ω)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (hp : L.data.target ≠ π OnePoint.infty)
    {g : ℂ → ℝ≥0∞}
    (D : ℕ → WeightedCollar base.physicalDomain π base.dust L.data.target g)
    (hnest : ∀ n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀ V ∈ 𝓝 L.data.target, ∃ k : ℕ,
      ∀ n ≥ k, closure (D n).region ⊆ V)
    (hanchor : Disjoint base.anchor (closure (D 0).region))
    (hfinite : OnePoint.infty ∉ closure (D 0).region)
    (hcontours : ∀ n, L.data.gateContours n = frontier (D n).region)
    (f : base.quotientDomain → Sphere) (hf : Continuous f) (W : Set Sphere)
    (hgate : ∀ n, L.data.gateSets n = Subtype.val '' (f ⁻¹' closure W))
    (F₀ : ℂ → ℂ)
    (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain))
    (hF₀m : Measurable F₀)
    (hF₀smooth : ContDiffOn ℝ (⊤ : ℕ∞) F₀
      (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain))
    (hF : ∀ x : base.quotientDomain, f x ∈ closure W →
      f x = (F₀ (finiteCoord (physicalValue base.domainEquiv base.basePoint x.val)) : Sphere))
    (c : ℂ) (r : ℝ≥0)
    (houtside : ∀ z : ℂ, (z : Sphere) ∈ base.physicalDomain → (r : ℝ) < dist (F₀ z) c)
    {R d₀ : ℝ} (hR : 0 ≤ R) (hd₀ : 0 < d₀)
    (hgap : ∀ z : ℂ, (z : Sphere) ∈ closure W →
      d₀ ≤ Metric.infDist z (Metric.closedBall c (r : ℝ))) :
    ∃ B : ℝ≥0, ∀ᶠ n in atTop,
      ∃ J : ℂ ≃ₜ ℂ, (D n).region = ((↑) : ℂ → Sphere) '' jordanInterior J ∧
      ∃ Q : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J)
        (meanBudgetTolerance B R (d₀ / 4)),
        Nonempty (RecursiveMeanOutput hsch Q F₀ hF₀ c r R (d₀ / 4)) := by
  have hanti : Antitone (fun n => (D n).region) :=
    antitone_nat_of_succ_le (fun n => subset_closure.trans (hnest n))
  have hintersection : (⋂ n, closure (D n).region) ⊆ {L.data.target} := by
    intro x hx
    by_contra hxp
    have hpx : L.data.target ≠ x := fun h => hxp h.symm
    obtain ⟨k, hk⟩ := hshrink {x}ᶜ (isClosed_singleton.isOpen_compl.mem_nhds hpx)
    exact hk k le_rfl (mem_iInter.mp hx k) rfl
  have hdisj : Disjoint base.quotientDomain base.dust := by
    rw [hdust]
    exact disjoint_compl_right
  obtain ⟨B, hB⟩ := finiteCoord_lipschitz_quotient_neighborhood π hπ base.physicalDomain
    (D 0).region ((D 0).infty_notMem_closure_region hπ hsurj hr)
  refine ⟨B, ?_⟩
  have hε : 0 < meanBudgetTolerance B R (d₀ / 4) :=
    meanBudgetTolerance_pos B hR (by positivity)
  filter_upwards [L.eventually_compact_reduction hselect harcs hU hG hπ hdisj
    (fun n => (D n).region) (fun n => (D n).isOpen_region hπ hclosed hsurj hr)
    (fun n => hanchor.mono_right ((hanti (Nat.zero_le n)).trans subset_closure))
    (fun n => (D n).point_mem_region hsurj hp) hanti hintersection hε] with n hn
  have hboundary : ∀ z ∈ frontier (jordanInterior (D n).disk),
      (z : Sphere) ∈ base.physicalDomain :=
    fun z hz => ((D n).level_good z ((D n).frontier_level hz)).1
  obtain ⟨J, hJ⟩ := exists_jordan_quotient_collar hsch base.physicalDomain π hπ hclosed
    hsurj hr (D n).disk hboundary
    (fun hx => hfinite (closure_mono (hanti (Nat.zero_le n)) hx))
  obtain ⟨C⟩ := (D n).exists_regular_inward_collar hcollar
  have hbJ : L.data.target ∈ ((↑) : ℂ → Sphere) '' jordanInterior J :=
    hJ ▸ (D n).point_mem_region hsurj hp
  have hinfty : π OnePoint.infty ∉ closure (((↑) : ℂ → Sphere) '' jordanInterior J) := by
    rw [← hJ]
    exact (D n).infty_notMem_closure_region hπ hsurj hr
  obtain ⟨Q⟩ := hn
  let Q' : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J)
      (meanBudgetTolerance B R (d₀ / 4)) := hJ ▸ Q
  have hBn : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹'
          ((((↑) : ℂ → Sphere) '' jordanInterior J) \ {L.data.target}))) := by
    apply hB.mono
    apply image_mono
    intro z hz
    have hzn : π (z : Sphere) ∈ (D n).region := by
      change π (z : Sphere) ∈ π '' (((↑) : ℂ → Sphere) '' jordanInterior (D n).disk)
      rw [hJ]
      exact hz.2.1
    exact ⟨hz.1, hanti (Nat.zero_le n) hzn⟩
  have hCclosed : ∀ k, IsClosed (L.data.gateContours k) := by
    intro k
    rw [hcontours]
    exact isClosed_frontier
  have hCK : ∀ k, IsClosed (L.data.gateContours k ∩ L.data.gateSets k) := by
    intro k
    rw [hcontours, hgate]
    apply isClosed_contour_gate isClosed_frontier ?_ hf isClosed_closure
    intro x hx
    obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ :=
      (D k).frontier_region_subset hπ ((D k).isOpen_region hπ hclosed hsurj hr) hx
    rw [← he ⟨(z : Sphere), ((D k).level_good z hz).1⟩]
    exact (base.domainEquiv _).property
  have hstart := Q'.physical_start_distance_of_inter_closed hCclosed hCK n
    (by rw [← hJ, hcontours]; exact Subset.rfl) f W (hgate n) F₀ hF c r d₀ hgap
  refine ⟨J, hJ, Q', ?_⟩
  exact Q'.exists_mean_exclusion hsch hsep hcoarea hG hU hdense hdust hπ hclosed hsurj hr he
    hbad C hJ hbJ hinfty B hBn hR hd₀
    (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain) (hG.preimage OnePoint.continuous_coe)
    hboundary (fun _ hz => hz) F₀ hF₀ hF₀m hF₀smooth c r houtside hstart

end CircleDomainRigidity

end

end OAI
