import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCanonicalLimit
import Mathlib.Analysis.SpecificLimits.Basic
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCompactSubsequence

namespace OAI

/-! Existence of the outgoing exterior is uniform on compact sets of shooting parameters. -/

open Set Filter
namespace DefocusingNLS

theorem radialExterior_compact_exists {K : Type*} [MetricSpace K] [CompactSpace K]
    (q m : K → ℂ) (hqcont : Continuous q) (hmcont : Continuous m) (l : ℝ)
    (hq : ∀ x, -1 < (q x).re)
    (hannulus : ∀ x, ∃ δ ρ : ℝ, 0 < δ ∧ δ < ‖m x‖ ∧ ‖m x‖+2*δ < 1 ∧ ρ < 1 ∧
      (∀ t, l ≤ t → ‖(radialFreeSlowJet (q x) (m x) t).1‖+2*δ ≤ ρ) ∧
      ∀ t, l ≤ t → δ < ‖(radialFreeSlowJet (q x) (m x) t).1‖) :
    ∀ᶠ (n : ℕ) in atTop, ∀ x, HasRadialExterior (-2*q x-1/(n : ℂ)) n (m x) l := by
  classical
  by_contra h
  obtain ⟨r,hr,y,y₀,hylim,hy⟩ := radial_compact_bad_subsequence
    (fun n x => HasRadialExterior (-2*q x-1/(n : ℂ)) n (m x) l) h
  have hqlim := hqcont.continuousAt.tendsto.comp hylim
  have hmlim := hmcont.continuousAt.tendsto.comp hylim
  have hν : Tendsto (fun i => -2*q (y i)-1/(r i : ℂ)) atTop (nhds (-2*q y₀)) := by
    simpa only [Function.comp_def,sub_zero] using!
      (hqlim.const_mul (-2)).sub
        ((tendsto_one_div_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1/(n : ℂ)) atTop (nhds 0)).comp hr.tendsto_atTop)
  obtain ⟨δ,ρ,hδ,hδm,hsmall,hρ,hupper,hlower⟩ := hannulus y₀
  have hex := (radialExteriorCanonical_H_limit_subsequence r hr
    (fun i => -2*q (y i)-1/(r i : ℂ)) (fun i => m (y i))
    (q y₀) (m y₀) (hq y₀) hν hmlim δ ρ l hδ hδm hsmall hρ hupper hlower).1
  obtain ⟨i,hi⟩ := hex.exists
  exact hy i hi

end DefocusingNLS

end OAI
