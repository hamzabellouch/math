import OAI.Analysis.CircleDomains.Selection.AnchoredDustBlock

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

theorem exists_path_replacing_finite_limit_block
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
    (n : ℕ) (p : Fin n → Sphere)
    (hpB : ∀i, p i ∈ B) (hp : ∀i, p i ≠ π OnePoint.infty)
    (Γ : Fin (n+1) → ℕ → TaggedPhysicalPath d)
    (hΓ : ∀i k, AllowedTaggedPath d ν N ((Γ i k).1.val, (Γ i k).2))
    (hΓF : ∀k, (Γ 0 k).1.val ⊥ ∈ F ∩ d.quotientDomain)
    (hΓH : ∀k, (Γ (Fin.last n) k).1.val ⊤ ∈ H ∩ d.quotientDomain)
    (hstart : ∀i : Fin n, Tendsto (fun k => (Γ i.succ k).1.val ⊥) atTop (𝓝 (p i)))
    (hend : ∀i : Fin n, Tendsto (fun k => (Γ i.castSucc k).1.val ⊤) atTop (𝓝 (p i)))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (A : Fin (n+1) → ℝ≥0∞) (hA : ∀i, A i < ∞)
    (hcost : ∀i, Tendsto (fun k => physicalTollCost d g m (Γ i k).1) atTop (𝓝 (A i)))
    (J : Fin n → ℝ≥0∞) (hpaid : ∀i, m (p i) ≤ J i)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧ ρ.val ⊤ ∈ H ∩ d.quotientDomain ∧
      physicalTollCost d g m ρ ≤ (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
  cases n with
  | zero =>
      have hlt : A 0 < A 0 + ENNReal.ofReal η :=
        ENNReal.lt_add_right (hA 0).ne (ENNReal.ofReal_pos.mpr hη).ne'
      obtain ⟨k, hk⟩ := ((hcost 0).eventually (gt_mem_nhds hlt)).exists
      exact ⟨(Γ 0 k).1, (Γ 0 k).2, hΓ 0 k, hΓF k, hΓH k, by simpa using hk.le⟩
  | succ n =>
      exact exists_path_replacing_anchored_dust_block
        hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense
        ν N F H hF hH n p hpB hp Γ hΓ hΓF hΓH hstart hend
        g hg henergy m hm A hA hcost J hpaid w hw hpos hpoint hη

end CircleDomainRigidity

end

end OAI
