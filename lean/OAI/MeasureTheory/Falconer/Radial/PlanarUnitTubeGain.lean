import OAI.MeasureTheory.Falconer.Geometry.PlanarSlopeBalls
import OAI.MeasureTheory.Falconer.Estimates.PlanarGain

namespace OAI

/-! # The planar Furstenberg consequence for unit-direction tube covers -/

namespace Falconer
open Set MeasureTheory
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem planar_unit_tube_gain
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (X W : Type) [MeasurableSpace X] [MeasurableSpace W]
      (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
      (p : X → Space 2) (q : W → Space 2) (E : X → W → Prop),
      Measurable p → Measurable q → MeasurableSet {z : X × W | E z.1 z.2} →
      (∀ x, ‖p x‖ ≤ 1/4) → (∀ w, ‖q w‖ = 1) →
      (∀ w, dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
      (∀ c r, δ ≤ r → (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ δ^(-η)*r^f) →
      (∀ c r, δ ≤ r → (ν : Measure W).real {w | dist (q w) c ≤ 2*r} ≤ δ^(-η)*r^b) →
    ∀ (κ : Type) (J : W → Finset κ) (a : κ → Space 2),
      (∀ w, ((J w).card : ℝ) ≤ δ^(-b-η)) →
      (∀ x w, E x w → ∃ i ∈ J w, ‖perpendicularPart (q w) (p x-a i)‖ ≤ C*δ) →
      (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) ≤ δ^η := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := planar_measure_projection_gain hpublished hb hb' hbf hf ((3/2)*C)
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro δ hδ hδsmall X W _ _ μ ν p q E hp hq hE hpbound hqunit hqchart hpball hqball κ J a hJ hcover
  have hpos (w : W) : 0 < q w 0 := (planarSlope_small_of_axis_close (hqchart w)).1
  have hslope (w : W) : |planarSlope (q w)| ≤ 1/2 :=
    (planarSlope_small_of_axis_close (hqchart w)).2
  let A : W → Finset ℝ := fun w => (J w).image (fun i => planarIntercept (q w) (a i))
  refine hgain δ hδ hδsmall X W μ ν p (fun w => planarSlope (q w)) E hp
    (by unfold planarSlope; fun_prop) hE
    (fun x => ⟨(PiLp.norm_apply_le (p x) 0).trans (hpbound x),
      (PiLp.norm_apply_le (p x) 1).trans (hpbound x)⟩) hslope hpball ?_ A ?_ ?_
  · intro c r hr
    exact (measureReal_mono (μ := (ν : Measure W))
      (planar_slope_ball_subset q hqunit hpos c r)).trans (hqball _ r hr)
  · intro w
    exact (Nat.cast_le.mpr (Finset.card_image_le)).trans (hJ w)
  · intro x w hx
    obtain ⟨i,hi,ht⟩ := hcover x w hx
    refine ⟨planarIntercept (q w) (a i),Finset.mem_image.mpr ⟨i,hi,rfl⟩,?_⟩
    simpa only [mul_assoc] using planar_tube_strip (hpos w).ne' (hslope w) ht

end Falconer

end OAI
