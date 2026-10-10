import OAI.Analysis.CircleDomains.Topology.CollarDustAvoidance
import OAI.Analysis.CircleDomains.Sobolev.SphericalAreaLocalization

namespace OAI

/-! Spherical-energy forms of the two collar constructions. The outer
neighborhoods and local energy bounds are derived, and all new interior
dust contacts belong to one of the original paths. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] in
private theorem exists_sphere_open_closure_inside {p : Sphere} {U : Set Sphere}
    (hU : U ∈ 𝓝 p) : ∃V : Set Sphere, IsOpen V ∧ p ∈ V ∧ closure V ⊆ U := by
  obtain ⟨C, hC, hCc, hCU⟩ := exists_mem_nhds_isClosed_subset hU
  exact ⟨interior C, isOpen_interior, mem_interior_iff_mem_nhds.mpr hC,
    (closure_minimal interior_subset hCc).trans hCU⟩

theorem exists_spherical_twoEnded_collar
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
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p q : Sphere) (hpB : p ∈ B) (hqB : q ∈ B)
    (hpq : p ≠ q)
    (hp : p ≠ π OnePoint.infty) (hq : q ≠ π OnePoint.infty)
    (hstart : Tendsto (fun n => (Γ n).1.val ⊥) atTop (𝓝 p))
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 q))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = p ∧ ρ.val ⊤ = q ∧
      interiorPhysicalTollCost d g m ρ ≤ A + ENNReal.ofReal η ∧
      ρ.val '' Ioo (⊥ : PathTime) ⊤ ∩ d.dust ⊆ ⋃n, range (Γ n).1.val := by
  obtain ⟨U, hpU, hUo, V, hqV, hVo, hUV⟩ := exists_open_nhds_disjoint_closure hpq
  obtain ⟨W, hWo, hpW, hW⟩ := exists_sphere_open_closure_inside
    (isClosed_singleton.isOpen_compl.mem_nhds hp)
  obtain ⟨Z, hZo, hqZ, hZ⟩ := exists_sphere_open_closure_inside
    (isClosed_singleton.isOpen_compl.mem_nhds hq)
  let O := U ∩ W
  let P := V ∩ Z
  have hOi : π OnePoint.infty ∉ closure O := fun h =>
    (hW (closure_mono inter_subset_right h)) rfl
  have hPi : π OnePoint.infty ∉ closure P := fun h =>
    (hZ (closure_mono inter_subset_right h)) rfl
  let S := d.dust \ ⋃n, range (Γ n).1.val
  have hS : Disjoint S d.quotientDomain := by
    apply Set.disjoint_left.mpr
    intro x hx hxu
    exact Set.disjoint_left.mp hdisj hxu hx.1
  have hav (n : ℕ) (t : PathTime) : (Γ n).1.val t ∉ S := by
    intro h
    exact h.2 (mem_iUnion.mpr ⟨n, mem_range_self t⟩)
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC, havoid⟩ := exists_twoEnded_splicing_avoiding_dust
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
    ν N Γ hΓ p q hpB hqB hp hq hstart hend O P (hUo.inter hWo) (hVo.inter hZo)
    ⟨hpU, hpW⟩ ⟨hqV, hqZ⟩
    (hUV.mono (inter_subset_left.trans subset_closure) (inter_subset_left.trans subset_closure))
    g hg (planar_energy_quotient_neighborhood_finite π hπ hOi g hg henergy)
    (planar_energy_quotient_neighborhood_finite π hπ hPi g hg henergy)
    m hm S hS hav A hA hcost w hw hpos hpoint hη
  refine ⟨ρ, θ, hρ, hρ0, hρ1, hC, ?_⟩
  rintro x ⟨⟨t, ht, rfl⟩, hx⟩
  by_contra h
  exact havoid t ht ⟨hx, h⟩

theorem exists_spherical_oneEnded_collar
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
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set Sphere) (hF : F ⊆ d.quotientDomain) (hstart : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : Sphere) (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 p))
    (hpF : p ∉ closure F)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η ∧
      ρ.val '' Iio (⊤ : PathTime) ∩ d.dust ⊆ ⋃n, range (Γ n).1.val := by
  obtain ⟨O, hOo, hpO, hO⟩ := exists_sphere_open_closure_inside
    ((isClosed_closure.union isClosed_singleton).isOpen_compl.mem_nhds
      (show p ∉ closure F ∪ {π OnePoint.infty} from fun h => h.elim hpF hp))
  have hOi : π OnePoint.infty ∉ closure O := fun h =>
    hO h (Or.inr rfl)
  have hFO : Disjoint F O := by
    apply Set.disjoint_left.mpr
    intro x hx hxO
    exact hO (subset_closure hxO) (Or.inl (subset_closure hx))
  let S := d.dust \ ⋃n, range (Γ n).1.val
  have hS : Disjoint S d.quotientDomain := by
    apply Set.disjoint_left.mpr
    intro x hx hxu
    exact Set.disjoint_left.mp hdisj hxu hx.1
  have hav (n : ℕ) (t : PathTime) : (Γ n).1.val t ∉ S := by
    intro h
    exact h.2 (mem_iUnion.mpr ⟨n, mem_range_self t⟩)
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC, havoid⟩ := exists_oneEnded_splicing_avoiding_dust
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
    ν N Γ hΓ F hF hstart p hpB hp hend O hOo hpO hFO
    g hg (planar_energy_quotient_neighborhood_finite π hπ hOi g hg henergy)
    m hm S hS hav A hA hcost w hw hpos hpoint hη
  refine ⟨ρ, θ, hρ, hρ0, hρ1, hC, ?_⟩
  rintro x ⟨⟨t, ht, rfl⟩, hx⟩
  by_contra h
  exact havoid t ht ⟨hx, h⟩

end CircleDomainRigidity

end

end OAI
