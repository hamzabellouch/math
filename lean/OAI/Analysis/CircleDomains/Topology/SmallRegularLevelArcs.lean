import OAI.Analysis.CircleDomains.Topology.RegularLevelArcs
import OAI.Analysis.CircleDomains.Topology.SmallCollarArcs

namespace OAI

/-! Small weighted joining arcs on a regular level through any prescribed
point, with endpoints specified directly in the plane. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_small_regular_level_arcs {f : ℂ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {t : ℝ} {z : ℂ}
    (hz : f z = t) (hregular : fderiv ℝ f z ≠ 0)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g)
    (hfinite : (∫⁻w in {w | f w = t}, g w ∂(μH[1] : Measure ℂ)) < ∞)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧
      ∀ x ∈ V ∩ {w | f w = t}, ∀ y ∈ V ∩ {w | f w = t},
        ∃ ρ : RectifiablePath ℂ, ρ.val ⊥ = x ∧ ρ.val ⊤ = y ∧
          range ρ.val ⊆ {w | f w = t} ∧ (∫⁻w, g w ∂pathOccupation ρ) < ε := by
  obtain ⟨γ, U, hU, hzU, hcover, hrange, hinj, hcost⟩ :=
    exists_finite_cost_regular_level_arc hf hz hregular g hfinite
  obtain ⟨r, hr⟩ := hcover ⟨hzU, hz⟩
  have htime : (∫⁻s, g (γ.val s) ∂pathLengthMeasure γ) < ∞ := by
    rwa [← lintegral_pathOccupation γ hg]
  obtain ⟨W, hW, hrW, hsmall⟩ :=
    exists_small_collar_arcs γ g hg htime r (fun s h => hinj h) hε
  refine ⟨U ∩ W, hU.inter hW, ⟨hzU, hr ▸ hrW⟩, ?_⟩
  intro x hx y hy
  obtain ⟨ρ, hρ0, hρ1, hρrange, hρcost⟩ :=
    hsmall x ⟨hx.1.2, hcover ⟨hx.1.1, hx.2⟩⟩ y ⟨hy.1.2, hcover ⟨hy.1.1, hy.2⟩⟩
  exact ⟨ρ, hρ0, hρ1, hρrange.trans hrange, hρcost⟩

end CircleDomainRigidity

end

end OAI
