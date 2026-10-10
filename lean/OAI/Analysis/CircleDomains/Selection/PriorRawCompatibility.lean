import OAI.Analysis.CircleDomains.Modulus.RawBarrierCompatibility
import OAI.Analysis.CircleDomains.Selection.PriorLevelFamily
import OAI.Analysis.CircleDomains.Rigidity.ENNRealBoundaryTrace
import OAI.Analysis.CircleDomains.Selection.BandContraction

namespace OAI

/-! Raw barrier compatibility for smooth finite-energy representatives
of the earlier coordinates. The tagged-path inequality and band budget
give compatibility using planar coarea, analytic measurability on finite
tori, and arcs in connected open subsets. -/

open Set Function MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem raw_barrier_compatibility_with_prior_levels
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
    (u : Sphere → ℝ) (hu : ∀x ∈ d.quotientDomain, u x ∈ Icc 0 1)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (hband : ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[d.quotientDomain] s) -
      liminf u (𝓝[d.quotientDomain] s)) ≤ 4 * m s)
    (n : ℕ) (labels : Fin (n + 1) → ℕ)
    (hN : (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle)))
      (N n labels) = 0) :
    (volume.prod (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle))))
      (freeComponentFailure F (circleBandGraph d.quotientDomain u)
        (fun i => Q.graph i) labels) = 0 := by
  have htrace := (boundaryTrace_of_ennreal_budget hu hBclosure hm hband).2
  apply raw_barrier_compatibility_of_finite_level_payments hLusin d hU hG hdisj
    π hπ hsurj hfiber he hB hTD hbad hBU hUB hF hFB (hFB.trans hBclosure) harcs
    (fun i => Q.graph i)
    Q.closed
    (fun i x t => by rw [hlevels]; rfl) g m
    Q.length
    (fun i => Q.weighted i g hg henergy) hm hmF hweights
    (fun i x => by simpa only [hlevels, mem_preimage, Prod.swap_prod_mk] using hpoint i x)
    ν N u (realBoundaryTrace d.quotientDomain u)
    (fun x hx => by rw [abs_of_nonneg (hu x hx).1]; exact (hu x hx).2)
    hpay (fun x hx => htrace x (hFB hx) (hmF x hx)) n labels hN

end CircleDomainRigidity

end

end OAI
