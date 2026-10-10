import OAI.Probability.SLE.Loewner.SlitCapacityChart
import OAI.Probability.SLE.Mass.HalfPlaneZeroMass

namespace OAI

/-! Every nontrivial simple attached slit has strictly positive capacity.
The proof rules out a zero-mass inverse displacement. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology

namespace SLEExactGauge

theorem simple_slit_exists_positive_capacity_chart
    (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    ∃ (G F : ℂ → ℂ) (c : ℝ), 0<c ∧
      BijOn G (upperHalfPlane \ range p) upperHalfPlane ∧
      DifferentiableOn ℂ G (upperHalfPlane \ range p) ∧
      DifferentiableOn ℂ F upperHalfPlane ∧
      MapsTo F upperHalfPlane (upperHalfPlane \ range p) ∧
      (∀ z ∈ upperHalfPlane \ range p, F (G z)=z) ∧
      (∀ z ∈ upperHalfPlane, G (F z)=z) ∧
      Tendsto (fun z : ℂ => z*(G z-z)) (cocompact ℂ) (𝓝 (c:ℂ)) ∧
      Tendsto (fun z : ℂ => F z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1) ∧
      (∀ z ∈ upperHalfPlane \ range p, (G z).im ≤ z.im) := by
  obtain ⟨G,F,c,hc,hG,hdG,hdF,hmF,hl,hr,hcoef,hn,hheight⟩ :=
    simple_slit_exists_nonnegative_capacity_chart p hi h0 hH
  have hcpos : 0<c := by
    by_contra hnot
    have hc0 : c=0 := le_antisymm (le_of_not_gt hnot) hc
    have hFcoef := inverse_hydrodynamic_coefficient hcoef hn hr
    rw [hc0,ofReal_zero,neg_zero] at hFcoef
    have hnonneg (z : ℂ) (hz : z ∈ upperHalfPlane) : 0 ≤ (F z-z).im := by
      have hh := normalized_halfPlane_height hdF (hmF.mono_right sdiff_subset) hn hz
      simpa only [sub_im] using sub_nonneg.mpr hh
    have he := holomorphic_zero_hydrodynamic_mass (hdF.sub differentiableOn_id) hnonneg hFcoef
    have hp1 : p 1 ∈ upperHalfPlane := hH 1 (by norm_num)
    have hF1 : F (p 1)=p 1 := sub_eq_zero.mp (he (p 1) hp1)
    have hm := hmF hp1
    rw [hF1] at hm
    exact hm.2 (mem_range_self 1)
  exact ⟨G,F,c,hcpos,hG,hdG,hdF,hmF,hl,hr,hcoef,hn,hheight⟩

end SLEExactGauge

end

end OAI
