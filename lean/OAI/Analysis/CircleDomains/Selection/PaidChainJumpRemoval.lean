import OAI.Analysis.CircleDomains.Selection.PositiveTollJumpRemoval
import OAI.Analysis.CircleDomains.Modulus.MixedChainNormalization

namespace OAI

/-! Removing a new jump level for arbitrary finite paid chains.
Normalization preserves the total cost and the actual new disks, so the
previously proved grouped-code estimate applies without a pattern hypothesis. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable {I K : Type*} [Fintype I] [MeasurableSpace C(PathTime, Sphere)]

theorem exists_mesh_preserving_mixed_chain_lower_bound
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
    ∃ε : ℝ, 0 < ε ∧ ∀W : K → Set Sphere,
      (∀k, (W k ∩ B).Nonempty) → (∀k, Metric.diam (W k) ≤ ε) →
      ∀x ∈ F ∩ d.quotientDomain, ∀y ∈ H ∩ d.quotientDomain, ∀c,
        PaidChain (physicalJumpEdge d ν N g m (Sum.elim O W)
          (Sum.elim T (fun k => fixedWidthJumpToll B m r τ (W k)))) x y c →
        ENNReal.ofReal (β-Δ) ≤ c := by
  obtain ⟨ε, hε, hbound⟩ := exists_mesh_preserving_positive_toll_chain_lower_bound
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense hinfty
    ν N F H O hF hH hO g hg henergy m hm r hτ T w hw hpos hpoint hΔ hΔβ hlower hrpos hTpos
  refine ⟨ε, hε, ?_⟩
  intro W hW hmesh x hx y hy c hc
  obtain ⟨n, P, Z, hZ, hcost, _, hfrom⟩ := exists_grouped_code_of_paid_chain
    d hU hdisj ν N B O W hW T r τ g hg m hm hpoint hc hx.2 hy.2
  have hstart := jumpBlockCode_initial_eq d ν N B {y} O P Z hZ
  have hend := jumpBlockCode_terminal_eq d ν N B {x} O P Z hZ
  have hZa := reanchor_jumpBlockCode d ν N B {x} {y} F H O P Z hZ
    (hstart.symm ▸ hx) (hend.symm ▸ hy)
  have hmeshZ : ∀b i, Metric.diam (Z.disks b i) ≤ ε := by
    intro b i
    obtain ⟨k, hk⟩ := hfrom b i
    rw [hk]
    exact hmesh k
  rw [← hcost]
  exact hbound n P Z hZa hmeshZ

end CircleDomainRigidity

end

end OAI
