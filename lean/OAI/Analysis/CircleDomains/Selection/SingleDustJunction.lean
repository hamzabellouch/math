import OAI.Analysis.CircleDomains.Topology.SphericalCollarSplicing
import OAI.Analysis.CircleDomains.Modulus.JoinedJunctionCost

namespace OAI

/-! Replace two true-path sequences meeting at a collapsing dust junction.
Both outer anchors stay in the domain; the junction is paid exactly once. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_path_through_single_dust_junction
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (F H : Set Sphere) (hF : F ⊆ d.quotientDomain) (hH : H ⊆ d.quotientDomain)
    (p : Sphere) (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    (hpF : p ∉ closure F) (hpH : p ∉ closure H)
    (Γ Δ : ℕ → TaggedPhysicalPath d)
    (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (hΔ : ∀n, AllowedTaggedPath d ν N ((Δ n).1.val, (Δ n).2))
    (hΓF : ∀n, (Γ n).1.val ⊥ ∈ F) (hΔH : ∀n, (Δ n).1.val ⊤ ∈ H)
    (hΓend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 p))
    (hΔstart : Tendsto (fun n => (Δ n).1.val ⊥) atTop (𝓝 p))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (A C : ℝ≥0∞) (hA : A < ∞) (hC : C < ∞)
    (hcostΓ : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (hcostΔ : Tendsto (fun n => physicalTollCost d g m (Δ n).1) atTop (𝓝 C))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ ∈ H ∧
      physicalTollCost d g m ρ ≤ A + C + m p + ENNReal.ofReal η := by
  have hhalf : 0 < η/2 := by positivity
  obtain ⟨α, θα, hα, hα0, hα1, hαcost, _⟩ := exists_spherical_oneEnded_collar
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
    ν N Γ hΓ F hF hΓF p hpB hp hΓend hpF g hg henergy m hm A hA hcostΓ
    w hw hpos hpoint hhalf
  let Δr := fun n => reversedTaggedPhysicalPath d (Δ n)
  have hΔr (n : ℕ) : AllowedTaggedPath d ν N ((Δr n).1.val, (Δr n).2) :=
    allowedTaggedPath_reversed d ν N ((Δ n).1.val, (Δ n).2) (hΔ n) hpoint
  have hΔrH (n : ℕ) : (Δr n).1.val ⊥ ∈ H := by
    change reversedPath (Δ n).1.val ⊥ ∈ H
    rw [reversedPath_zero]
    exact hΔH n
  have hΔrend : Tendsto (fun n => (Δr n).1.val ⊤) atTop (𝓝 p) := by
    convert hΔstart using 1
    funext n
    exact reversedPath_one (Δ n).1.val
  have hcostΔr : Tendsto (fun n => physicalTollCost d g m (Δr n).1) atTop (𝓝 C) := by
    convert hcostΔ using 1
    funext n
    exact physicalTollCost_reversed d g m (Δ n).1
  obtain ⟨β, θβ, hβ, hβ0, hβ1, hβcost, _⟩ := exists_spherical_oneEnded_collar
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
    ν N Δr hΔr H hH hΔrH p hpB hp hΔrend hpH g hg henergy m hm C hC hcostΔr
    w hw hpos hpoint hhalf
  rw [preterminalToll_eq_interior_of_initial_zero α.val m (hm _ (hF hα0))] at hαcost
  rw [preterminalToll_eq_interior_of_initial_zero β.val m (hm _ (hH hβ0))] at hβcost
  obtain ⟨βr, θr, hβr, hβr0, hβr1, hβrcost⟩ :=
    exists_allowed_reversed_interior_cost d ν N (β, θβ) hβ g m hpoint
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hρcost⟩ := exists_allowed_joined_junction_cost
    d hU ν N (α, θα) (βr, θr) hα hβr (hα1.trans (hβ1.symm.trans hβr0.symm))
    g hg m hpoint
  have hρF : ρ.val ⊥ ∈ F := hρ0.symm ▸ hα0
  have hρH : ρ.val ⊤ ∈ H := hρ1.symm ▸ hβr1.symm ▸ hβ0
  refine ⟨ρ, θ, hρ, hρF, hρH, ?_⟩
  rw [← interiorPhysicalTollCost_eq_full d g m ρ (hm _ (hF hρF)) (hm _ (hH hρH)),
    hρcost, hβrcost, hα1]
  have herr : ENNReal.ofReal (η/2) + ENNReal.ofReal (η/2) = ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_add hhalf.le hhalf.le]
    congr 1
    ring
  calc
    interiorPhysicalTollCost d g m α + interiorPhysicalTollCost d g m β + m p ≤
        (A + ENNReal.ofReal (η/2)) + (C + ENNReal.ofReal (η/2)) + m p :=
      add_le_add (add_le_add hαcost hβcost) le_rfl
    _ = A + C + m p + ENNReal.ofReal η := by rw [← herr]; ac_rfl

end CircleDomainRigidity

end

end OAI
