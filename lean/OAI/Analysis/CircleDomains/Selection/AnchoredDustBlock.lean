import OAI.Analysis.CircleDomains.Selection.AnchoredJunctionChain
import OAI.Analysis.CircleDomains.Selection.AnchorTailAttachment
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

theorem exists_path_replacing_anchored_dust_block
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
    (hUB : Disjoint d.quotientDomain B) (hdense : Dense d.quotientDomain)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (F H : Set Sphere) (hF : frontier F ⊆ d.quotientDomain)
    (hH : frontier H ⊆ d.quotientDomain)
    (n : ℕ) (p : Fin (n+1) → Sphere)
    (hpB : ∀i, p i ∈ B) (hp : ∀i, p i ≠ π OnePoint.infty)
    (Γ : Fin (n+2) → ℕ → TaggedPhysicalPath d)
    (hΓ : ∀i k, AllowedTaggedPath d ν N ((Γ i k).1.val, (Γ i k).2))
    (hΓF : ∀k, (Γ 0 k).1.val ⊥ ∈ F ∩ d.quotientDomain)
    (hΓH : ∀k, (Γ (Fin.last (n+1)) k).1.val ⊤ ∈ H ∩ d.quotientDomain)
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
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧ ρ.val ⊤ ∈ H ∩ d.quotientDomain ∧
      physicalTollCost d g m ρ ≤ (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
  have hh : 0 < η/2 := by positivity
  let A' : Fin (n+1) → ℝ≥0∞ := fun i => A i.castSucc
  let J' : Fin n → ℝ≥0∞ := fun i => J i.castSucc
  have inside (S : Set Sphere) (hS : frontier S ⊆ d.quotientDomain)
      (i : Fin (n+1)) (hin : p i ∈ closure S) : p i ∈ interior S := by
    by_contra hn
    exact Set.disjoint_left.mp hUB (hS ⟨hin, hn⟩) (hpB i)
  have hj (i : Fin n) : m (p i.castSucc) ≤ J' i := hpaid i.castSucc
  have hf : p 0 ∈ interior F ∨ ∀ε : ℝ, 0 < ε →
      ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧ ρ.val ⊤ = p 0 ∧
        interiorPhysicalTollCost d g m ρ ≤ A' 0 + ENNReal.ofReal ε := by
    by_cases hin : p 0 ∈ closure F
    · exact Or.inl (inside F hF 0 hin)
    · right
      intro ε hε
      have hout : p 0 ∉ closure (F ∩ d.quotientDomain) :=
        fun h => hin (closure_mono inter_subset_left h)
      obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc, _⟩ := exists_spherical_oneEnded_collar
        hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
        ν N (Γ 0) (hΓ 0) (F ∩ d.quotientDomain) inter_subset_right hΓF
        (p 0) (hpB 0) (hp 0) (hend 0) hout
        g hg henergy m hm (A 0) (hA 0) (hcost 0) w hw hpos hpoint hε
      rw [preterminalToll_eq_interior_of_initial_zero ρ.val m (hm _ hρ0.2)] at hc
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
  have hleft := exists_allowed_anchored_junction_prefix
    d hU ν N g hg m hpoint F hF n p A' J' hj hf hs hh
  have hright : p (Fin.last n) ∈ interior H ∨
      ∃ (β : FinitePhysicalPath d.domainEquiv d.basePoint) (θβ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (β.val, θβ) ∧ β.val ⊥ ∈ H ∩ d.quotientDomain ∧
        β.val ⊤ = p (Fin.last n) ∧
        interiorPhysicalTollCost d g m β ≤ A (Fin.last (n+1)) + ENNReal.ofReal (η/2) := by
    by_cases hin : p (Fin.last n) ∈ closure H
    · exact Or.inl (inside H hH _ hin)
    · right
      let Δ := fun k => reversedTaggedPhysicalPath d (Γ (Fin.last (n+1)) k)
      have hΔ (k : ℕ) : AllowedTaggedPath d ν N ((Δ k).1.val, (Δ k).2) :=
        allowedTaggedPath_reversed d ν N
          ((Γ (Fin.last (n+1)) k).1.val, (Γ (Fin.last (n+1)) k).2)
          (hΓ _ k) hpoint
      have hΔH (k : ℕ) : (Δ k).1.val ⊥ ∈ H ∩ d.quotientDomain := by
        change reversedPath (Γ (Fin.last (n+1)) k).1.val ⊥ ∈ H ∩ d.quotientDomain
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
      have hout : p (Fin.last n) ∉ closure (H ∩ d.quotientDomain) :=
        fun h => hin (closure_mono inter_subset_left h)
      obtain ⟨β, θβ, hβ, hβ0, hβ1, hβc, _⟩ := exists_spherical_oneEnded_collar
        hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
        ν N Δ hΔ (H ∩ d.quotientDomain) inter_subset_right hΔH
        (p (Fin.last n)) (hpB _) (hp _) hΔend hout
        g hg henergy m hm (A (Fin.last (n+1))) (hA _) hΔcost w hw hpos hpoint hh
      rw [preterminalToll_eq_interior_of_initial_zero β.val m (hm _ hβ0.2)] at hβc
      exact ⟨β, θβ, hβ, hβ0, hβ1, hβc⟩
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := exists_allowed_anchor_tail_attachment
    d hU hdisj hdense ν N g hg m hm hpoint F H hF hH (p (Fin.last n))
    ((∑i, A' i) + (∑i, J' i) + ENNReal.ofReal (η/2))
    (A (Fin.last (n+1)) + ENNReal.ofReal (η/2)) (J (Fin.last n)) (hpaid _) hleft hright
  refine ⟨ρ, θ, hρ, hρ0, hρ1, ?_⟩
  have herr : ENNReal.ofReal (η/2) + ENNReal.ofReal (η/2) = ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_add hh.le hh.le]
    congr 1
    ring
  have hsA := Fin.sum_univ_castSucc A
  have hsJ := Fin.sum_univ_castSucc J
  convert hc using 1
  rw [hsA, hsJ, ← herr]
  dsimp [A', J']
  ac_rfl

end CircleDomainRigidity

end

end OAI
