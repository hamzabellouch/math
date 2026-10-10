import OAI.MeasureTheory.Falconer.Radial.PublishedHeavyPlates
import OAI.MeasureTheory.Falconer.Estimates.UniformLowerPlanes

namespace OAI

/-! # The precise published cover applied to an original Frostman probability -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem unit_heavy_plate_cover (hpublished : PublishedHeavyHyperplanes)
    {d : ℕ} (hd : 3 ≤ d) (μ : ProbabilityMeasure (Space d)) {s C : ℝ}
    (hs : 1/2 < s-((d-2:ℕ):ℝ)) (hs' : s-((d-2:ℕ):ℝ) < 1) (hC : 0 ≤ C)
    (hbounded : ∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ < 1)
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ S : Finset (Space d × ℝ), (∀ p ∈ S, ‖p.1‖ = 1) ∧
        (S.card:ℝ) ≤ K*δ^(-heavyPlateExponent (s-((d-2:ℕ):ℝ))) ∧
        ∀ w : Space d, ‖w‖ = 1 → ∀ t : ℝ,
          ENNReal.ofReal (δ^(heavyPlateExponent (s-((d-2:ℕ):ℝ)))) ≤
            (μ : Measure (Space d)) {x | |inner ℝ w x-t| ≤ δ} →
          ∃ p ∈ S, ∀ x : Space d, ‖x‖ < 1 → |inner ℝ w x-t| ≤ δ →
            |inner ℝ p.1 x-p.2| ≤ K*δ^(1/4:ℝ) := by
  have hα : 0 ≤ s-((d-2:ℕ):ℝ) := by linarith only [hs]
  have hbound : ∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ ≤ 1 := hbounded.mono (fun _ h => h.le)
  obtain ⟨D,hD,hplane⟩ := uniform_lower_plane_frostman (k := d-2)
    (μ : Measure (Space d)) (by norm_num) hC hα hbound hfrost
  obtain ⟨K,hK,hcover⟩ := hpublished d hd (s-((d-2:ℕ):ℝ)) D hs hs' hD
  refine ⟨K,hK,?_⟩
  intro δ hδ hδ1
  obtain ⟨S,hunit,hcard,hcoverS⟩ := hcover μ δ hδ hδ1 hbounded
    (fun V hV p => hplane V hV.le p δ hδ hδ1)
  refine ⟨S,hunit,hcard,?_⟩
  intro w hw t hheavy
  obtain ⟨p,hp,hpcover⟩ := hcoverS w hw t hheavy
  refine ⟨p,hp,?_⟩
  intro x hx hxw
  apply (hpcover x hx hxw).trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    (heavyPlate_cover_exponent hs).le) (zero_le_one.trans hK)

end Falconer

end OAI
