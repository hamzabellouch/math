import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Selection.SmallAnchoredCoordinateFamily
import OAI.Analysis.CircleDomains.Uniformization.SelectedRealLimit
import OAI.Analysis.CircleDomains.Selection.ExteriorZeroAnchor
import OAI.Analysis.CircleDomains.Topology.AnchoredCollarFamily

namespace OAI

/-! Every non-point complementary component of the normalized limit
contains one of the countably many marked disks. -/

open Set Function Filter Metric MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem exists_selected_normal_limit
    (hcross : UnitDiskAlternatingContinua)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (harea : ExteriorCoefficientAreaTheorem) (hmontel : MontelExhaustion)
    (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hconn : IsConnected d.physicalDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀ x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (hinfEStar : π OnePoint.infty ∈ interior EStar)
    (hBimage : d.dust = π '' d.physicalDomainᶜ)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    : ∃ S : Set Sphere, S.Countable ∧ S ⊆ d.dust ∧
      ∃ F : FiniteTransfer.CountableRealCoordinates d.physicalDomain π (fun s : S => s.val),
      ∃ M : FiniteTransfer.RealModelExhaustion F
        (FiniteTransfer.markedNeighborhoods (fun s : S => s.val)) FiniteTransfer.modelError,
      ∃ L : FiniteTransfer.AssignedRealModelLimit M,
        ∀ p ∈ (extendAtInfinity L.function '' d.physicalDomain)ᶜ,
          connectedComponentIn (extendAtInfinity L.function '' d.physicalDomain)ᶜ p = {p} ∨
          ∃ s : S, ((↑) : ℂ → Sphere) '' closedBall (L.center s) (L.radius s) ⊆
            connectedComponentIn (extendAtInfinity L.function '' d.physicalDomain)ᶜ p := by
  obtain ⟨D, hnest, hshrink, hED⟩ := exists_anchored_collar_family
    hcoarea hsard hsch d.physicalDomain π hπ hclosed hsurj hr d.dust hB hTD
    hbad hinfty d.anchor hE (hdisj.mono_left hEU)
  obtain ⟨S, hSc, hSB, F, _, hFcompat, hsmall⟩ := exists_small_anchored_coordinates
    hcross hcoarea hLusin hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he
    hB hTD hBU hdense hinfty hbad hinf EStar hE hEU hEStar hEStarE hinfE hBimage
    D hnest hshrink hED hfiber harcs C hC hderiv hstandard hpath ω hω hωsum hdual hlift
  let : Countable S := hSc.to_subtype
  obtain ⟨R, hR, hRE⟩ := exists_exterior_in_quotient_neighborhood hπ hinfEStar
  obtain ⟨M, hRM⟩ := FiniteTransfer.exists_real_model_exhaustion_large_radius
    hsard hsch hcompact hfinite hG hconn hinf hπ hclosed hsurj hr
    (hBimage ▸ hTD) F hFcompat (FiniteTransfer.markedNeighborhoods (fun s : S => s.val))
    (FiniteTransfer.markedNeighborhoods_nhds _) FiniteTransfer.modelError
    FiniteTransfer.modelError_pos R
  obtain ⟨L⟩ := M.exists_assigned_limit harea hmontel hhurwitz hzero hsard hsch hG hconn
  refine ⟨S, hSc, hSB, F, M, L, ?_⟩
  intro p hp
  apply L.singleton_or_marked_disk_of_small_anchored hsard hsch harea hG hconn
    FiniteTransfer.modelError_tendsto hπ hr EStar ?_ ?_ hp
  · intro z hz
    apply hRE
    have hz' : ‖z‖ = 2 * M.radius := by simpa only [mem_sphere, dist_zero_right] using hz
    rw [hz']
    linarith [M.radius_pos]
  · intro b hb
    apply hsmall b
    simpa only [← hBimage, Subtype.range_val] using hb

end CircleDomainRigidity

end

end OAI
