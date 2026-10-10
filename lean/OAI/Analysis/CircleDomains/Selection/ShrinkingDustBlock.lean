import OAI.Analysis.CircleDomains.Selection.AnchoredDustBlock
import OAI.Analysis.CircleDomains.Topology.ShrinkingBlockCompactness

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

theorem exists_path_replacing_shrinking_dust_block
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
    (hinfty : π OnePoint.infty ∉ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (F H : Set Sphere) (hF : frontier F ⊆ d.quotientDomain)
    (hH : frontier H ⊆ d.quotientDomain)
    (n : ℕ) (Γ : Fin (n+2) → ℕ → TaggedPhysicalPath d)
    (hΓ : ∀i k, AllowedTaggedPath d ν N ((Γ i k).1.val, (Γ i k).2))
    (hΓF : ∀k, (Γ 0 k).1.val ⊥ ∈ F ∩ d.quotientDomain)
    (hΓH : ∀k, (Γ (Fin.last (n+1)) k).1.val ⊤ ∈ H ∩ d.quotientDomain)
    (V : Fin (n+1) → ℕ → Set Sphere)
    (hleft : ∀i k, (Γ i.castSucc k).1.val ⊤ ∈ V i k)
    (hright : ∀i k, (Γ i.succ k).1.val ⊥ ∈ V i k)
    (hmeet : ∀i k, (V i k ∩ B).Nonempty)
    (hdiam : ∀i, Tendsto (fun k => Metric.diam (V i k)) atTop (𝓝 0))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (r : ℝ≥0∞) {τ : ℝ} (hτ : 0 < τ) (M : ℝ≥0∞) (hM : M < ∞)
    (hbudget : ∀k, (∑i, physicalTollCost d g m (Γ i k).1) +
      (∑i, fixedWidthJumpToll B m r τ (V i k)) ≤ M)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧
      ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧ ρ.val ⊤ ∈ H ∩ d.quotientDomain ∧
      physicalTollCost d g m ρ ≤ M + ENNReal.ofReal η := by
  obtain ⟨s, p, A, J, hs, hpB, hend, hstart, hcost, hJcost, hpaid, htotal⟩ :=
    exists_finite_shrinking_block_limits d B hB g m r hτ n Γ V hleft hright hmeet hdiam M hbudget
  have hp (i : Fin (n+1)) : p i ≠ π OnePoint.infty := by
    intro heq
    exact hinfty (heq ▸ hpB i)
  have hA (i : Fin (n+2)) : A i < ∞ := by
    have hi : A i ≤ ∑j, A j := Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ _)
    exact lt_of_le_of_lt (hi.trans ((le_add_right le_rfl).trans htotal)) hM
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := exists_path_replacing_anchored_dust_block
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense
    ν N F H hF hH n p hpB hp (fun i k => Γ i (s k))
    (fun i k => hΓ i (s k)) (fun k => hΓF (s k)) (fun k => hΓH (s k)) hstart hend
    g hg henergy m hm A hA hcost J hpaid w hw hpos hpoint hη
  exact ⟨ρ, θ, hρ, hρ0, hρ1, hc.trans (add_le_add htotal le_rfl)⟩

end CircleDomainRigidity

end

end OAI
