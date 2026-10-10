import OAI.Analysis.CircleDomains.Selection.BoundedJumpRemoval
import OAI.Analysis.CircleDomains.Selection.JumpBlockCountBound

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

theorem exists_mesh_preserving_chain_lower_bound
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
    {δ : ℝ} (hδ : 0 < δ) (hrfloor : ENNReal.ofReal δ ≤ r)
    (hT : ∀i, ENNReal.ofReal δ ≤ T i) :
    ∃ε : ℝ, 0 < ε ∧ ∀n : ℕ, ∀P : BoundedBlockPattern I n, ∀Z : JumpBlockCode d P,
      IsJumpBlockCode d ν N B F H O P Z →
      (∀b i, Metric.diam (Z.disks b i) ≤ ε) →
      ENNReal.ofReal (β-Δ) ≤ jumpBlockCost d B g m r τ T P Z := by
  obtain ⟨K, hK⟩ := exists_uniform_block_pattern_bound d B g m r τ T hδ hrfloor hT
    (M := ENNReal.ofReal (β-Δ)) ENNReal.ofReal_lt_top
  obtain ⟨ε, hε, hmeshBound⟩ := exists_mesh_preserving_bounded_chain_lower_bound
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense hinfty
    ν N F H O hF hH hO g hg henergy m hm r hτ T w hw hpos hpoint hΔ hΔβ hlower K
  refine ⟨ε, hε, fun n P Z hZ hmesh => ?_⟩
  by_contra hlow
  have hc : jumpBlockCost d B g m r τ T P Z < ENNReal.ofReal (β-Δ) := lt_of_not_ge hlow
  obtain ⟨hold, hnew⟩ := hK n P Z hc.le
  have hc' := hmeshBound (reboundBlockPattern P hold hnew) (reboundJumpBlock d P hold hnew Z)
    (reboundJumpBlock_valid d ν N B F H O P hold hnew Z hZ) hmesh
  exact hc.not_ge (by simpa using hc')

end CircleDomainRigidity

end

end OAI
