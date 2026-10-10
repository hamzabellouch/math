import OAI.Analysis.CircleDomains.Selection.PriorRawCompatibility

namespace OAI

/-! Compatibility of the smoothed coordinate follows from the proved
raw path-cost estimate and pointwise contraction of its dust bands. -/

open Set Function MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem smoothed_barrier_compatibility_with_prior_levels
    [MeasurableSpace C(PathTime, Sphere)]
    (hLusin : FiniteTorusAnalyticMeasurability)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {B F : Set Sphere} (hB : IsCompact B) (hTD : IsTotallyDisconnected B)
    (hbad : π '' d.physicalDomainᶜ ⊆ B)
    (hBU : Bᶜ ⊆ d.quotientDomain) (hUB : Disjoint d.quotientDomain B)
    (hBclosure : B ⊆ closure d.quotientDomain)
    (hF : MeasurableSet F) (hFB : F ⊆ B)
    (harcs : ∀C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (Q : PriorLevelFamily d.physicalDomain π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      Q.graph i)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : (∑'x, m x ^ 2) ≠ ∞) (hmF : ∀x ∈ F, m x = 0)
    (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (ν : Measure Sphere)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u : Sphere → ℝ) (hu : ∀x, u x ∈ Icc 0 1)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (hband : ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[d.quotientDomain] s) -
      liminf u (𝓝[d.quotientDomain] s)) ≤ 4 * m s)
    (v : PhysicalRealCoordinate d π)
    (hcontract : ∀s ∈ B,
      liminf u (𝓝[d.quotientDomain] s) ≤ liminf v.quotient (𝓝[d.quotientDomain] s) ∧
      limsup v.quotient (𝓝[d.quotientDomain] s) ≤ limsup u (𝓝[d.quotientDomain] s))
    (n : ℕ) (labels : Fin (n + 1) → ℕ)
    (hN : (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle)))
      (N n labels) = 0) :
    (volume.prod (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle))))
      (freeComponentFailure F (circleBandGraph d.quotientDomain v.quotient)
        (fun i => Q.graph i) labels) = 0 := by
  apply band_contraction_preserves_compatibility
    (volume.prod (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle)))) F
    (circleBandGraph d.quotientDomain v.quotient) (circleBandGraph d.quotientDomain u)
    (fun i => Q.graph i) labels
  · intro x hx
    apply circle_band_subset_of_real_band
    apply real_band_subset_of_liminf_limsup d.quotientDomain u v.quotient
      hu v.quotient_unit (hBclosure (hFB hx)) (hcontract x (hFB hx)).1 (hcontract x (hFB hx)).2
  · exact raw_barrier_compatibility_with_prior_levels hLusin d hU hG hdisj
      π hπ hsurj hfiber he hB hTD hbad hBU hUB hBclosure hF hFB harcs Q hlevels
      g hg henergy m hm hmF hweights hpoint ν N u (fun x _ => hu x) hpay hband n labels hN

end CircleDomainRigidity

end

end OAI
