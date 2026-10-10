import OAI.Analysis.CircleDomains.Selection.JumpLevelRemoval
import OAI.Analysis.CircleDomains.Selection.FiniteJumpFloor

namespace OAI

/-! Remove all new shrinking jumps from a fixed finite old-jump pattern.
All blocks use one common subsequence, so the total budget is retained. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable {I : Type*} [Fintype I] [MeasurableSpace C(PathTime, Sphere)]

theorem exists_mesh_preserving_positive_toll_chain_lower_bound
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
    (F H : Set Sphere) (O : I → Set Sphere)
    (hF : frontier F ⊆ d.quotientDomain) (hH : frontier H ⊆ d.quotientDomain)
    (hO : ∀i, frontier (O i) ⊆ d.quotientDomain)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (r : ℝ≥0∞) {τ : ℝ} (hτ : 0 < τ) (T : I → ℝ≥0∞)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {β Δ : ℝ} (hΔ : 0 < Δ) (hΔβ : Δ < β)
    (hlower : ∀x ∈ F ∩ d.quotientDomain, ∀y ∈ H ∩ d.quotientDomain, ∀c,
      PaidChain (physicalJumpEdge d ν N g m O T) x y c → ENNReal.ofReal β ≤ c)
    (hrpos : 0 < r) (hTpos : ∀i, 0 < T i) :
    ∃ε : ℝ, 0 < ε ∧ ∀n : ℕ, ∀P : BoundedBlockPattern I n, ∀Z : JumpBlockCode d P,
      IsJumpBlockCode d ν N B F H O P Z →
      (∀b i, Metric.diam (Z.disks b i) ≤ ε) →
      ENNReal.ofReal (β-Δ) ≤ jumpBlockCost d B g m r τ T P Z := by
  obtain ⟨δ, hδ, hrfloor, hT⟩ := exists_common_positive_jump_floor r hrpos T hTpos
  exact exists_mesh_preserving_chain_lower_bound
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense hinfty
    ν N F H O hF hH hO g hg henergy m hm r hτ T w hw hpos hpoint hΔ hΔβ hlower hδ hrfloor hT

end CircleDomainRigidity

end

end OAI
