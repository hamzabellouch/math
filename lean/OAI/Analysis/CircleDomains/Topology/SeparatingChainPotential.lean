import OAI.Analysis.CircleDomains.Selection.ProgressiveJumpSystems
import OAI.Analysis.CircleDomains.Selection.SymmetricJumpEdges
import OAI.Analysis.CircleDomains.Selection.SupportedJumpTolls
import OAI.Analysis.CircleDomains.Selection.ChainPotentialBands
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! The actual truncated chain distance separates the anchor and terminal
collar, obeys every true-path cost inequality, and has pointwise dust bands
bounded by four times the original toll. No barrier function is assumed. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_separating_chain_potential
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
    (F H : Set Sphere)
    (hF : frontier F ⊆ d.quotientDomain) (hH : frontier H ⊆ d.quotientDomain)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (htrue : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ F → Γ.1.val ⊤ ∈ H → ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g m Γ.1)
    (hBU : Bᶜ ⊆ d.quotientDomain) (S : Set Sphere) (hS : IsOpen S) (hBS : B ⊆ S)
    (hm₂ : (∑' x, m x ^ 2) ≠ ∞) :
    ∃u : Sphere → ℝ,
      (∀x, u x ∈ Icc 0 1) ∧
      (∀x ∈ F ∩ d.quotientDomain, u x = 0) ∧
      (∀x ∈ H ∩ d.quotientDomain, u x = 1) ∧
      (∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
        Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
        ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1) ∧
      ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[d.quotientDomain] s) -
        liminf u (𝓝[d.quotientDomain] s)) ≤ 4 * m s := by
  classical
  let q : ℕ → ℝ := fun n => (1/2)^n
  have hq (n : ℕ) : 0 < q n := pow_pos (by norm_num) n
  have hqlim : Tendsto q atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hρlim : Tendsto (fun n => ENNReal.ofReal (q n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hqlim
  obtain ⟨J, _, _, _, hlevels, hlower⟩ := exists_progressive_barrier_jump_system
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense hinfty
    ν N F H hF hH g hg henergy m hm w hw hpos hpoint htrue hBU S hS hBS
    (fun n => ENNReal.ofReal (q n)) (fun n => ENNReal.ofReal_pos.mpr (hq n)) q q hq hq
  let R : Sphere → Sphere → ℝ≥0∞ → Prop := fun x y c => ∃n, (J n).edge d ν N g m x y c
  have hR (x y : Sphere) (c : ℝ≥0∞) (h : R x y c) : R y x c := by
    obtain ⟨n, hn⟩ := h
    exact ⟨n, physicalJumpEdge_symmetric d ν N g m (J n).region (J n).toll hpoint hn⟩
  let E := F ∩ d.quotientDomain
  refine ⟨realChainPotential R E, realChainPotential_mem_Icc R E, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change (chainPotential R E x).toReal = 0
    rw [chainPotential_anchor R hx]
    rfl
  · intro y hy
    have hsep : chainPotential R E y = 1 := chainPotential_separated R (fun x hx c hc => by
      simpa using hlower x hx y hy c hc)
    change (chainPotential R E y).toReal = 1
    rw [hsep]
    rfl
  · intro Γ hΓ hx hy
    apply realChainPotential_difference R hR
    exact ⟨0, physicalJumpEdge_of_path d ν N g m (J 0).region (J 0).toll Γ hΓ hx hy⟩
  · intro s hs
    choose k V hVo hcover _ _ hdiam _ hedge using hlevels
    have hindex (n : ℕ) : ∃i, s ∈ V n i := mem_iUnion.mp (hcover n hs)
    choose i hi using hindex
    let W : ℕ → Set Sphere := fun n => V n (i n)
    have hW (n : ℕ) : W n ∈ 𝓝 s := (hVo n (i n)).mem_nhds (hi n)
    have hWsmall (n : ℕ) : W n ⊆ Metric.ball s (q n) := by
      intro x hx
      exact (Metric.dist_le_diam_of_mem (Bornology.IsBounded.subset isCompact_univ.isBounded (subset_univ _))
        hx (hi n)).trans_lt (hdiam n (i n))
    have hmsupport (x : Sphere) (hx : x ∉ B) : m x = 0 := hm x (hBU hx)
    have hj (n : ℕ) (x : Sphere) (hx : x ∈ d.quotientDomain ∩ W n)
        (y : Sphere) (hy : y ∈ d.quotientDomain ∩ W n) :
        R x y (max (ENNReal.ofReal (q n)) (neighborhoodTollSup m (Metric.thickening (q n) (W n)))) := by
      have h := hedge n (i n) x ⟨hx.2, hx.1⟩ y ⟨hy.2, hy.1⟩
      rw [fixedWidthJumpToll_eq_neighborhood B _ m hmsupport] at h
      exact ⟨n+1, h⟩
    have hsclosure : s ∈ closure d.quotientDomain := by
      rw [hdense.closure_eq]
      trivial
    exact chainPotential_boundary_band R hR E d.quotientDomain hm₂ hsclosure hW hWsmall
      hqlim hqlim hρlim hj

end CircleDomainRigidity

end

end OAI
