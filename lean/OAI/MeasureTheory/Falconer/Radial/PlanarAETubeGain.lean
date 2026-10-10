import OAI.MeasureTheory.Falconer.Radial.PlanarUnitTubeGain
import OAI.MeasureTheory.Falconer.Geometry.PlanarChartRepair

namespace OAI

/-! # The planar tube gain on the actual supports of the two laws -/

namespace Falconer
open Set MeasureTheory
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem planar_ae_tube_gain
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (X W : Type) [MeasurableSpace X] [MeasurableSpace W]
      (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
      (p : X → Space 2) (q : W → Space 2) (E : X → W → Prop),
      Measurable p → Measurable q → MeasurableSet {z : X × W | E z.1 z.2} →
      (∀ᵐ x ∂(μ : Measure X), ‖p x‖ ≤ 1/4) →
      (∀ᵐ w ∂(ν : Measure W), ‖q w‖ = 1 ∧
        dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
      (∀ c r, δ ≤ r → (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ δ^(-η)*r^f) →
      (∀ c r, δ ≤ r → (ν : Measure W).real {w | dist (q w) c ≤ 2*r} ≤ δ^(-η)*r^b) →
    ∀ (κ : Type) (J : W → Finset κ) (a : κ → Space 2),
      (∀ w, ((J w).card : ℝ) ≤ δ^(-b-η)) →
      (∀ x w, E x w → ∃ i ∈ J w, ‖perpendicularPart (q w) (p x-a i)‖ ≤ C*δ) →
      (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) ≤ δ^η := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := planar_unit_tube_gain hpublished hb hb' hbf hf C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro δ hδ hδsmall X W _ _ μ ν p q E hp hq hE hpb hqb hpball hqball κ J a hJ hcover
  let F : X → W → Prop := fun x w => E x w ∧ ‖p x‖ ≤ 1/4 ∧
    (‖q w‖ = 1 ∧ dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4)
  have hP : MeasurableSet {x | ‖p x‖ ≤ 1/4} := measurableSet_le hp.norm measurable_const
  have hQ : MeasurableSet {w | ‖q w‖ = 1 ∧
      dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4} :=
    (measurableSet_eq_fun hq.norm measurable_const).inter
      (measurableSet_le (hq.dist measurable_const) measurable_const)
  have hF : MeasurableSet {z : X × W | F z.1 z.2} :=
    hE.inter ((hP.preimage measurable_fst).inter (hQ.preimage measurable_snd))
  have hpb' (c : Space 2) (r : ℝ) (hr : δ ≤ r) :
      (μ : Measure X).real {x | dist (boundedPlanarPoint (p x)) c ≤ r} ≤ δ^(-η)*r^f := by
    have he : {x | dist (boundedPlanarPoint (p x)) c ≤ r} =ᵐ[(μ : Measure X)]
        {x | dist (p x) c ≤ r} := by
      filter_upwards [hpb] with x hx
      simp only [boundedPlanarPoint_eq hx]
    rw [measureReal_congr he]
    exact hpball c r hr
  have hqb' (c : Space 2) (r : ℝ) (hr : δ ≤ r) :
      (ν : Measure W).real {w | dist (chartedPlanarDirection (q w)) c ≤ 2*r} ≤ δ^(-η)*r^b := by
    have he : {w | dist (chartedPlanarDirection (q w)) c ≤ 2*r} =ᵐ[(ν : Measure W)]
        {w | dist (q w) c ≤ 2*r} := by
      filter_upwards [hqb] with w hw
      simp only [chartedPlanarDirection_eq hw]
    rw [measureReal_congr he]
    exact hqball c r hr
  have hsmall : (∫ w, ∫ x, @ite ℝ (F x w) (Classical.propDecidable (F x w)) 1 0
      ∂(μ : Measure X) ∂(ν : Measure W)) ≤ δ^η := by
    apply hgain δ hδ hδsmall X W μ ν (fun x => boundedPlanarPoint (p x))
      (fun w => chartedPlanarDirection (q w)) F
      (boundedPlanarPoint_measurable.comp hp) (chartedPlanarDirection_measurable.comp hq) hF
      (fun x => boundedPlanarPoint_norm (p x)) (fun w => chartedPlanarDirection_unit (q w))
      (fun w => chartedPlanarDirection_chart (q w)) hpb' hqb' κ J a hJ
    intro x w hx
    obtain ⟨i,hi,ht⟩ := hcover x w hx.1
    refine ⟨i,hi,?_⟩
    rw [boundedPlanarPoint_eq hx.2.1,chartedPlanarDirection_eq hx.2.2]
    exact ht
  have he : (∫ w, ∫ x, @ite ℝ (F x w) (Classical.propDecidable (F x w)) 1 0
      ∂(μ : Measure X) ∂(ν : Measure W)) =
      (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) := by
    apply integral_congr_ae
    filter_upwards [hqb] with w hw
    apply integral_congr_ae
    filter_upwards [hpb] with x hx
    simp only [F,hx,hw,and_true]
  rw [he] at hsmall
  exact hsmall

end Falconer

end OAI
