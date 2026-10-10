import OAI.Analysis.CircleDomains.Topology.GatedCollarSplicing
import OAI.Analysis.CircleDomains.Topology.LocalInterposedCollars
import OAI.Analysis.CircleDomains.Sobolev.SphericalAreaLocalization
import OAI.Analysis.CircleDomains.Selection.FirstEntryRange

namespace OAI

/-! Step 1 of the gated compatible-barrier argument: first-arrival
separation at the dust point implies separation at a finite collar. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_finite_gated_collar_cost_lower_bound
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (F : Set Sphere) (hF : F ⊆ d.quotientDomain)
    (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π B p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (hFD : Disjoint F (closure (D 0).region)) (K : ℕ → Set Sphere)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (hunit : ∀(ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) → ρ.val ⊥ ∈ F → ρ.val ⊤ = p →
      (∀t < (⊤ : PathTime), ρ.val t ≠ p) →
      GateRules (fun j => frontier (D j).region) K ρ.val →
      1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m) :
    ∃k : ℕ, ∀Γ : TaggedPhysicalPath d,
      AllowedTaggedPath d ν N (Γ.1.val, Γ.2) → Γ.1.val ⊥ ∈ F →
      Γ.1.val ⊤ ∈ frontier (D k).region →
      (∀j ≤ k, GateRule (frontier (D j).region) (K j) Γ.1.val) →
      ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g m Γ.1 := by
  classical
  by_contra hn
  push Not at hn
  choose Γ hΓ hΓF hΓend hΓgate hΓcost using hn
  have hD (n : ℕ) := (D n).isOpen_region hπ hclosed hsurj hr
  have hpD (n : ℕ) := (D n).point_mem_region hsurj hp
  have ha : Antitone (fun n => (D n).region) :=
    antitone_nat_of_succ_le (fun n => subset_closure.trans (hnest n))
  have hFDn (n : ℕ) : Disjoint F (closure (D n).region) :=
    hFD.mono_right (closure_mono (ha (Nat.zero_le n)))
  have hprefix (n : ℕ) := exists_allowed_first_entry_prefix_with_range d hU ν N (Γ n) (hΓ n)
    (hD n) (fun h => Set.disjoint_left.mp (hFDn n) (hΓF n) h)
    (frontier_subset_closure (hΓend n)) g hg m hpoint
  choose Δ hΔ hΔstart hΔend hΔrange hΔsub hΔcost using hprefix
  have hΔgate (n : ℕ) : GateRules (fun j => frontier (D j).region) K (Δ n).1.val := by
    intro j t ht
    by_cases hj : j ≤ n
    · obtain ⟨s, hs⟩ := hΔsub n (mem_range_self t)
      exact hs ▸ hΓgate n j hj s (hs.symm ▸ ht)
    · have hm := hnest n (closure_mono (ha (by omega : n+1 ≤ j)) (frontier_subset_closure ht))
      exact ((hΔrange n (mem_range_self t)) hm).elim
  have hcost (n : ℕ) : physicalTollCost d g m (Δ n).1 < ENNReal.ofReal ((1 : ℝ)/2) :=
    (hΔcost n).trans_lt (hΓcost n)
  obtain ⟨A, hA, s, hs, hlim⟩ := isCompact_Icc.tendsto_subseq
    (fun n => (show physicalTollCost d g m (Δ n).1 ∈ Icc 0 (ENNReal.ofReal ((1 : ℝ)/2)) from
      ⟨bot_le, (hcost n).le⟩))
  have hend : Tendsto (fun n => (Δ n).1.val ⊤) atTop (𝓝 p) := by
    apply tendsto_def.mpr
    intro V hV
    obtain ⟨k, hk⟩ := hshrink V hV
    filter_upwards [eventually_ge_atTop k] with n hn
    exact hk n hn (frontier_subset_closure (hΔend n))
  have havoid (n : ℕ) (t : PathTime) : (Δ n).1.val t ≠ p := by
    intro ht
    exact (hΔrange n (mem_range_self t)) (ht ▸ hpD n)
  have hgD := planar_energy_quotient_neighborhood_finite π hπ
    ((D 0).infty_notMem_closure_region hπ hsurj hr) g hg henergy
  obtain ⟨E, hE0, hEn, hEl, hEs, hEa, _⟩ := exists_interposed_weighted_collars_of_local_energy
    hcoarea hsard hsch d.physicalDomain π hπ hclosed hsurj hr hB hbad D
    hnest hshrink (fun z : ℂ => g (z : Sphere))
    (hg.comp OnePoint.continuous_coe.measurable) hgD
  have hlevelAvoid (j : ℕ) (z : ℂ) (hz : (E j).function z = (E j).level) :
      π (z : Sphere) ∉ ({p} : Set Sphere) := by
    intro heq
    have hx : π (z : Sphere) ∈ d.quotientDomain := by
      rw [← he ⟨(z : Sphere), ((E j).level_good z hz).1⟩]
      exact (d.domainEquiv _).property
    exact Set.disjoint_left.mp hdisj ((mem_singleton_iff.mp heq) ▸ hx) hpDust
  have hpgate (j : ℕ) : p ∉ frontier (D j).region := by
    rw [(hD j).frontier_eq]
    exact fun h => h.2 (hpD j)
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC, hgate, hfirst'⟩ :=
    exists_weighted_oneEnded_splicing_preserving_gates d hU hG hdisj π hπ hclosed hsurj hr he
      ν N (fun n => Δ (s n)) (fun n => hΔ (s n)) F hF
      (fun n => (hΔstart (s n)) ▸ hΓF (s n)) p hp (hend.comp hs.tendsto_atTop)
      g hg m hm {p} (fun n t => havoid (s n) t)
      (fun j => frontier (D j).region) K (fun n => hΔgate (s n)) hpgate
      E hlevelAvoid hEa hEn hEs hEl
      (hFD.mono_right (hE0.trans subset_closure))
      A (hA.2.trans_lt ENNReal.ofReal_lt_top) hlim w hw hpos hpoint
      (η := (1 : ℝ)/4) (by norm_num)
  have hfirst (t : PathTime) (ht : t < ⊤) : ρ.val t ≠ p := hfirst' t ht
  have hcontr : (1 : ℝ≥0∞) < 1 := calc
    1 ≤ _ := hunit ρ θ hρ hρ0 hρ1 hfirst hgate
    _ ≤ A + ENNReal.ofReal ((1 : ℝ)/4) := hC
    _ ≤ ENNReal.ofReal ((1 : ℝ)/2) + ENNReal.ofReal ((1 : ℝ)/4) :=
      add_le_add hA.2 le_rfl
    _ < 1 := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (0 : ℝ) ≤ 1/4), ← ENNReal.ofReal_one,
        ENNReal.ofReal_lt_ofReal_iff zero_lt_one]
      norm_num
  exact (lt_irrefl _) hcontr

end CircleDomainRigidity

end

end OAI
