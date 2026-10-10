import OAI.Analysis.CircleDomains.Selection.PaidChainJumpRemoval
import OAI.Analysis.CircleDomains.Selection.SafeDustCover

namespace OAI

/-! A concrete new finite jump level inside the safe region. Its mesh may
be made arbitrarily small while retaining the old chain lower bound minus
the prescribed loss. Every new jump has positive toll and a domain boundary. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable {I : Type*} [Fintype I] [MeasurableSpace C(PathTime, Sphere)]

theorem exists_safe_new_jump_level
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
    (hrpos : 0 < r) (hTpos : ∀i, 0 < T i)
    (hBU : Bᶜ ⊆ d.quotientDomain) (S : Set Sphere) (hS : IsOpen S) (hBS : B ⊆ S)
    {mesh : ℝ} (hmesh : 0 < mesh) :
    ∃n : ℕ, ∃V : Fin n → Set Sphere,
      (∀i, IsOpen (V i)) ∧ B ⊆ ⋃i, V i ∧
      Pairwise (Disjoint on fun i => closure (V i)) ∧
      (∀i, closure (V i) ⊆ S) ∧ (∀i, Metric.diam (V i) < mesh) ∧
      (∀i, (V i ∩ B).Nonempty) ∧
      (∀i, frontier (V i) ⊆ d.quotientDomain) ∧
      (∀i, 0 < fixedWidthJumpToll B m r τ (V i)) ∧
      ∀x ∈ F ∩ d.quotientDomain, ∀y ∈ H ∩ d.quotientDomain, ∀c,
        PaidChain (physicalJumpEdge d ν N g m (Sum.elim O V)
          (Sum.elim T (fun i => fixedWidthJumpToll B m r τ (V i)))) x y c →
        ENNReal.ofReal (β-Δ) ≤ c := by
  obtain ⟨ε, hε, hbound⟩ := exists_mesh_preserving_positive_toll_chain_lower_bound
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense hinfty
    ν N F H O hF hH hO g hg henergy m hm r hτ T w hw hpos hpoint hΔ hΔβ hlower hrpos hTpos
  obtain ⟨n, V, hVo, hcover, hpair, hsafe, hdiam, hmeet, hfront⟩ :=
    exists_safe_small_dust_cover hB.isCompact hTD hS hBS (lt_min hε hmesh)
  refine ⟨n, V, hVo, hcover, hpair, hsafe, fun i => (hdiam i).trans_le (min_le_right _ _),
    hmeet, ?_, ?_, ?_⟩
  · intro i x hx
    apply hBU
    exact fun hxB => Set.disjoint_left.mp (hfront i) hx hxB
  · intro i
    exact hrpos.trans_le (le_max_left _ _)
  · intro x hx y hy c hc
    obtain ⟨k, P, Z, hZ, hcost, _, hfrom⟩ := exists_grouped_code_of_paid_chain
      d hU hdisj ν N B O V hmeet T r τ g hg m hm hpoint hc hx.2 hy.2
    have hstart := jumpBlockCode_initial_eq d ν N B {y} O P Z hZ
    have hend := jumpBlockCode_terminal_eq d ν N B {x} O P Z hZ
    have hZa := reanchor_jumpBlockCode d ν N B {x} {y} F H O P Z hZ
      (hstart.symm ▸ hx) (hend.symm ▸ hy)
    rw [← hcost]
    apply hbound k P Z hZa
    intro b i
    obtain ⟨j, hj⟩ := hfrom b i
    rw [hj]
    exact (hdiam j).le.trans (min_le_left _ _)

end CircleDomainRigidity

end

end OAI
