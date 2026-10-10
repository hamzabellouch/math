import OAI.Analysis.CircleDomains.Sobolev.SphereChartLipschitz
import OAI.Analysis.CircleDomains.Topology.SmallRegularLevelArcs
import OAI.Analysis.CircleDomains.Sobolev.LipschitzMappedCost

namespace OAI

/-! Arbitrarily short weighted arcs on a compact regular level, measured
in the fixed physical sphere metric. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem exists_small_sphere_regular_level_arcs {f : ℂ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {t : ℝ} (hreg : IsPlanarRegularValue f t)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hfinite : (∫⁻z in {z | f z = t}, g (z : Sphere) ∂(μH[1] : Measure ℂ)) < ∞)
    {z : ℂ} (hz : f z = t) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ V : Set Sphere, IsOpen V ∧ (z : Sphere) ∈ V ∧
      ∀x ∈ V ∩ (((↑) : ℂ → Sphere) '' {z | f z = t}),
      ∀y ∈ V ∩ (((↑) : ℂ → Sphere) '' {z | f z = t}),
        ∃ρ : RectifiablePath Sphere, ρ.val ⊥ = x ∧ ρ.val ⊤ = y ∧
          range ρ.val ⊆ ((↑) : ℂ → Sphere) '' {z | f z = t} ∧
          (∫⁻p, g p ∂pathOccupation ρ) < ε := by
  have hgc : Measurable (fun z : ℂ => g (z : Sphere)) :=
    hg.comp OnePoint.continuous_coe.measurable
  obtain ⟨γ, U, hU, hzU, hcover, hrange, hinj, hcost⟩ :=
    exists_finite_cost_regular_level_arc hf hz (hreg z hz)
      (fun z : ℂ => g (z : Sphere)) hfinite
  obtain ⟨L, hL⟩ := finite_sphere_chart_lipschitz_on_compact
    (isCompact_range γ.val.continuous)
  have hγ : ∀s, γ.val s ∈ range γ.val := fun s => mem_range_self s
  let β := lipschitzMappedPath γ ((↑) : ℂ → Sphere) hL hγ
  have hβcost : (∫⁻s, g (β.val s) ∂pathLengthMeasure β) < ∞ := by
    rw [← lintegral_pathOccupation β hg]
    apply lipschitzMappedPath_cost_lt_top γ ((↑) : ℂ → Sphere) hL hγ g hg
    rwa [← lintegral_pathOccupation γ hgc]
  obtain ⟨r, hr⟩ := hcover ⟨hzU, hz⟩
  have hβr : β.val r = (z : Sphere) := congrArg ((↑) : ℂ → Sphere) hr
  have hβinj : Injective β.val := OnePoint.coe_injective.comp hinj
  obtain ⟨W, hW, hrW, hsmall⟩ := exists_small_collar_arcs β g hg hβcost r
    (fun s h => hβinj h) hε
  refine ⟨W ∩ (((↑) : ℂ → Sphere) '' U),
    hW.inter (OnePoint.isOpen_image_coe.mpr hU),
    ⟨hβr ▸ hrW, mem_image_of_mem _ hzU⟩, ?_⟩
  intro x hx y hy
  have hmem : ∀v : Sphere, v ∈ ((↑) : ℂ → Sphere) '' U →
      v ∈ ((↑) : ℂ → Sphere) '' {z | f z = t} → v ∈ range β.val := by
    intro v hvU hv
    obtain ⟨a, ha, rfl⟩ := hv
    have haU : a ∈ U := by
      obtain ⟨b, hb, he⟩ := hvU
      exact (OnePoint.coe_injective he) ▸ hb
    obtain ⟨s, hs⟩ := hcover ⟨haU, ha⟩
    exact ⟨s, congrArg ((↑) : ℂ → Sphere) hs⟩
  obtain ⟨ρ, hρ0, hρ1, hρrange, hρcost⟩ :=
    hsmall x ⟨hx.1.1, hmem x hx.1.2 hx.2⟩ y ⟨hy.1.1, hmem y hy.1.2 hy.2⟩
  refine ⟨ρ, hρ0, hρ1, hρrange.trans ?_, hρcost⟩
  rintro p ⟨s, rfl⟩
  exact ⟨γ.val s, hrange (mem_range_self s), rfl⟩

end CircleDomainRigidity

end

end OAI
