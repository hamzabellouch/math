import OAI.Analysis.CircleDomains.Selection.CollapsingJunctionChain
import OAI.Analysis.CircleDomains.Selection.SingleDustJunction

namespace OAI

/-! A finite block of possibly repeated limiting dust junctions can be
replaced by one allowed true path. The original true-piece limits and one
paid toll per junction cover the replacement, up to any positive error. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_path_through_finite_dust_junctions
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
    (n : ℕ) (p : Fin (n+1) → Sphere)
    (hpB : ∀i, p i ∈ B) (hp : ∀i, p i ≠ π OnePoint.infty)
    (hpF : p 0 ∉ closure F) (hpH : p (Fin.last n) ∉ closure H)
    (Γ : Fin (n+2) → ℕ → TaggedPhysicalPath d)
    (hΓ : ∀i k, AllowedTaggedPath d ν N ((Γ i k).1.val, (Γ i k).2))
    (hΓF : ∀k, (Γ 0 k).1.val ⊥ ∈ F)
    (hΓH : ∀k, (Γ (Fin.last (n+1)) k).1.val ⊤ ∈ H)
    (hstart : ∀i : Fin (n+1), Tendsto (fun k => (Γ i.succ k).1.val ⊥) atTop (𝓝 (p i)))
    (hend : ∀i : Fin (n+1), Tendsto (fun k => (Γ i.castSucc k).1.val ⊤) atTop (𝓝 (p i)))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (A : Fin (n+2) → ℝ≥0∞) (hA : ∀i, A i < ∞)
    (hcost : ∀i, Tendsto (fun k => physicalTollCost d g m (Γ i k).1) atTop (𝓝 (A i)))
    (J : Fin (n+1) → ℝ≥0∞) (hpaid : ∀i, m (p i) ≤ J i)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ ∈ H ∧
      physicalTollCost d g m ρ ≤ (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
  have hh : 0 < η/2 := by positivity
  let A' : Fin (n+1) → ℝ≥0∞ := fun i => A i.castSucc
  let J' : Fin n → ℝ≥0∞ := fun i => J i.castSucc
  have hj (i : Fin n) : m (p i.castSucc) ≤ J' i := hpaid i.castSucc
  have hf (ε : ℝ) (hε : 0 < ε) :
      ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p 0 ∧
        interiorPhysicalTollCost d g m ρ ≤ A' 0 + ENNReal.ofReal ε := by
    obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc, _⟩ := exists_spherical_oneEnded_collar
      hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
      ν N (Γ 0) (hΓ 0) F hF hΓF (p 0) (hpB 0) (hp 0) (hend 0) hpF
      g hg henergy m hm (A 0) (hA 0) (hcost 0) w hw hpos hpoint hε
    rw [preterminalToll_eq_interior_of_initial_zero ρ.val m (hm _ (hF hρ0))] at hc
    exact ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩
  have hs (i : Fin n) (hne : p i.castSucc ≠ p i.succ) (ε : ℝ) (hε : 0 < ε) :
      ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (ρ.val, θ) ∧
        ρ.val ⊥ = p i.castSucc ∧ ρ.val ⊤ = p i.succ ∧
        interiorPhysicalTollCost d g m ρ ≤ A' i.succ + ENNReal.ofReal ε := by
    obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc, _⟩ := exists_spherical_twoEnded_collar
      hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
      ν N (Γ i.castSucc.succ) (hΓ _) (p i.castSucc) (p i.succ)
      (hpB _) (hpB _) hne (hp _) (hp _)
      (hstart i.castSucc) (hend i.succ) g hg henergy m hm
      (A i.castSucc.succ) (hA _) (hcost _) w hw hpos hpoint hε
    exact ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩
  obtain ⟨α, θα, hα, hα0, hα1, hαc⟩ := exists_allowed_collapsing_junction_prefix
    d hU ν N g hg m hpoint F n p A' J' hj hf hs hh
  let Δ := fun k => reversedTaggedPhysicalPath d (Γ (Fin.last (n+1)) k)
  have hΔ (k : ℕ) : AllowedTaggedPath d ν N ((Δ k).1.val, (Δ k).2) :=
    allowedTaggedPath_reversed d ν N
      ((Γ (Fin.last (n+1)) k).1.val, (Γ (Fin.last (n+1)) k).2)
      (hΓ _ k) hpoint
  have hΔH (k : ℕ) : (Δ k).1.val ⊥ ∈ H := by
    change reversedPath (Γ (Fin.last (n+1)) k).1.val ⊥ ∈ H
    rw [reversedPath_zero]
    exact hΓH k
  have hΔend : Tendsto (fun k => (Δ k).1.val ⊤) atTop (𝓝 (p (Fin.last n))) := by
    convert hstart (Fin.last n) using 1
    funext k
    exact reversedPath_one (Γ (Fin.last (n+1)) k).1.val
  have hΔcost : Tendsto (fun k => physicalTollCost d g m (Δ k).1)
      atTop (𝓝 (A (Fin.last (n+1)))) := by
    convert hcost (Fin.last (n+1)) using 1
    funext k
    exact physicalTollCost_reversed d g m (Γ (Fin.last (n+1)) k).1
  obtain ⟨β, θβ, hβ, hβ0, hβ1, hβc, _⟩ := exists_spherical_oneEnded_collar
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
    ν N Δ hΔ H hH hΔH (p (Fin.last n)) (hpB _) (hp _) hΔend hpH
    g hg henergy m hm (A (Fin.last (n+1))) (hA _) hΔcost w hw hpos hpoint hh
  rw [preterminalToll_eq_interior_of_initial_zero β.val m (hm _ (hH hβ0))] at hβc
  obtain ⟨βr, θr, hβr, hβr0, hβr1, hβrc⟩ :=
    exists_allowed_reversed_interior_cost d ν N (β, θβ) hβ g m hpoint
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := exists_allowed_joined_junction_cost
    d hU ν N (α, θα) (βr, θr) hα hβr (hα1.trans (hβ1.symm.trans hβr0.symm))
    g hg m hpoint
  have hρF : ρ.val ⊥ ∈ F := hρ0.symm ▸ hα0
  have hρH : ρ.val ⊤ ∈ H := hρ1.symm ▸ hβr1.symm ▸ hβ0
  refine ⟨ρ, θ, hρ, hρF, hρH, ?_⟩
  rw [← interiorPhysicalTollCost_eq_full d g m ρ (hm _ (hF hρF)) (hm _ (hH hρH)),
    hc, hβrc, hα1]
  have herr : ENNReal.ofReal (η/2) + ENNReal.ofReal (η/2) = ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_add hh.le hh.le]
    congr 1
    ring
  have hsA := Fin.sum_univ_castSucc A
  have hsJ := Fin.sum_univ_castSucc J
  calc
    interiorPhysicalTollCost d g m α + interiorPhysicalTollCost d g m β + m (p (Fin.last n)) ≤
        ((∑i, A' i) + (∑i, J' i) + ENNReal.ofReal (η/2)) +
        (A (Fin.last (n+1)) + ENNReal.ofReal (η/2)) + J (Fin.last n) :=
      add_le_add (add_le_add hαc hβc) (hpaid _)
    _ = (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
      rw [hsA, hsJ, ← herr]
      dsimp [A', J']
      ac_rfl

end CircleDomainRigidity

end

end OAI
