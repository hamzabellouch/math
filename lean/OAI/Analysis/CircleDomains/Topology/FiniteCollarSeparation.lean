import OAI.Analysis.CircleDomains.Topology.SphericalCollarSplicing
import OAI.Analysis.CircleDomains.Selection.FirstEntryRestriction

namespace OAI

/-! Step 1 of the ungated compatible-barrier argument: first-arrival
separation at the dust point implies separation at a finite collar. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_finite_collar_cost_lower_bound
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
    (F : Set Sphere) (hF : F ⊆ d.quotientDomain)
    (p : Sphere) (hpB : p ∈ B) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    (hpF : p ∉ closure F)
    (W : ℕ → Set Sphere) (hW : ∀n, IsOpen (W n)) (hpW : ∀n, p ∈ W n)
    (hFW : ∀n, Disjoint F (closure (W n)))
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (W n) ⊆ V)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (hunit : ∀(ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) → ρ.val ⊥ ∈ F → ρ.val ⊤ = p →
      (∀t < (⊤ : PathTime), ρ.val t ≠ p) →
      1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m) :
    ∃k : ℕ, ∀Γ : TaggedPhysicalPath d,
      AllowedTaggedPath d ν N (Γ.1.val, Γ.2) → Γ.1.val ⊥ ∈ F →
      Γ.1.val ⊤ ∈ frontier (W k) →
      ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g m Γ.1 := by
  classical
  by_contra hn
  push Not at hn
  choose Γ hΓ hΓF hΓend hΓcost using hn
  have hprefix (n : ℕ) := exists_allowed_first_entry_prefix d hU ν N (Γ n) (hΓ n)
    (hW n) (fun h => Set.disjoint_left.mp (hFW n) (hΓF n) h)
    (frontier_subset_closure (hΓend n)) g hg m hpoint
  choose Δ hΔ hΔstart hΔend hΔrange hΔcost using hprefix
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
    exact (hΔrange n (mem_range_self t)) (ht ▸ hpW n)
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC, htrace⟩ := exists_spherical_oneEnded_collar
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
    ν N (fun n => Δ (s n)) (fun n => hΔ (s n)) F hF
    (fun n => (hΔstart (s n)) ▸ hΓF (s n)) p hpB hp (hend.comp hs.tendsto_atTop) hpF
    g hg henergy m hm A (hA.2.trans_lt ENNReal.ofReal_lt_top) hlim w hw hpos hpoint
    (η := (1 : ℝ)/4) (by norm_num)
  have hfirst (t : PathTime) (ht : t < ⊤) : ρ.val t ≠ p := by
    intro heq
    have hmem := htrace ⟨⟨t, ht, heq⟩, hpDust⟩
    obtain ⟨n, z, hz⟩ := mem_iUnion.mp hmem
    exact havoid (s n) z hz
  have hcontr : (1 : ℝ≥0∞) < 1 := calc
    1 ≤ _ := hunit ρ θ hρ hρ0 hρ1 hfirst
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
