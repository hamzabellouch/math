import OAI.Probability.SLE.Gauge.RibbonStepSuccess
import OAI.Probability.SLE.Gauge.ExtendedRibbonStep

namespace OAI

/-! A measurable narrow physical prefix yields the exact actual history.
A successful uniform step yields the next such prefix and an actual mass
window between successive global first-front times. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates FirstFrontPassage BoundaryScaleLaw

/-- The path-space step event is deterministic once the chart and integer
front are fixed, although the actual Loewner history is random. -/
def ribbonPathStep (P : ℂ → ℂ) (C L : ℝ≥0) (ε k κ v c : ℝ) : Set C(ℝ≥0, ℂ) :=
  frontMassEvent (longitudinalCoordinate P closedRibbon k)
    (physicalPassageRegion (fun z => P ((k : ℂ) + z)) ribbonStepCompact C ε (ε / L))
    (P ((k : ℂ) + 1)) (ε / L) κ v c (physicalMiddleRegion P closedRibbon k ε)

lemma RibbonHistory.stepEvent_eq_ribbonPathStep
    {C L : ℝ≥0} {ε : ℝ} (d : RibbonHistory C L ε) (κ v c : ℝ) :
    d.stepEvent κ v c = ribbonPathStep d.chart C L ε d.front κ v c := rfl

lemma ribbonPathStep_measurable
    (P : ℂ → ℂ) (C L : ℝ≥0) (ε k κ v c : ℝ)
    (hplanar : PublishedPlanarDiskOpenness) (hε : ε ≤ 1 / 8) (hk : 1 ≤ k)
    (hemb : Topology.IsClosedEmbedding (fun z : closedRibbon => P z))
    (hP : ContinuousOn P closedRibbon)
    (hlower : ∀ z ∈ ribbonStepPatch k, ∀ w ∈ ribbonStepPatch k,
      dist z w ≤ L * dist (P z) (P w)) :
    MeasurableSet (ribbonPathStep P C L ε k κ v c) := by
  let Q := fun z : ℂ => P ((k : ℂ) + z)
  have hmap : MapsTo (fun z : ℂ => (k : ℂ) + z) ribbonStepCompact closedRibbon := by
    intro z hz
    change 0 ≤ k + z.re ∧ |0 + z.im| ≤ 1
    exact ⟨by linarith [hz.1], by simpa using hz.2.2.trans (by norm_num)⟩
  have hQ : ContinuousOn Q ribbonStepCompact :=
    hP.comp (continuous_const.add continuous_id).continuousOn hmap
  have hQl : ∀ u ∈ ribbonStepCompact, ∀ w ∈ ribbonStepCompact,
      dist u w ≤ L * dist (Q u) (Q w) := by
    intro u hu w hw
    simpa only [Q, dist_add_left] using
      hlower _ (translate_ribbonStepCompact hu) _ (translate_ribbonStepCompact hw)
  have hK := ribbonStepCompact_isCompact.image_of_continuousOn hQ
  have hp : ContinuousOn (longitudinalCoordinate P closedRibbon k) (Q '' ribbonStepCompact) :=
    ((Complex.continuous_re.comp_continuousOn
      (coordinateInverse_continuousOn_of_embedding P hemb.isEmbedding)).sub continuousOn_const).mono
      (by rintro _ ⟨z, hz, rfl⟩; exact ⟨(k : ℂ) + z, hmap hz, rfl⟩)
  have hV : IsOpen (physicalPassageRegion Q ribbonStepCompact C ε (ε / L)) := by
    have he : ribbonStepCompact ∩ passageCoordinateRegion C ε (ε / L) =
        interior ribbonStepCompact ∩ passageCoordinateRegion C ε (ε / L) := by
      apply Subset.antisymm
      · exact fun z hz => ⟨ribbonStepCompact_passage hε C (ε / L) hz, hz.2⟩
      · exact inter_subset_inter_left _ interior_subset
    unfold physicalPassageRegion
    rw [he]
    exact isOpen_image_coordinate_subset hplanar Q ribbonStepCompact _ hQ
      (lower_lipschitz_injOn _ _ L hQl)
      (isOpen_interior.inter (passageCoordinateRegion_isOpen C ε (ε / L)))
      (inter_subset_left.trans interior_subset)
  exact measurableSet_frontMassEvent _ _ _ _ κ v c _ _ hK.isClosed hp hV
    (image_mono inter_subset_left)

theorem actual_history_of_goodRibbonPrefix
    {C L : ℝ≥0} {ε : ℝ}
    (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (P : ℂ → ℂ)
    (hemb : Topology.IsClosedEmbedding (fun z : closedRibbon => P z))
    (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (hH : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane)
    (hescape : Tendsto (fun t : ℝ => ‖P (t : ℂ)‖) atTop atTop)
    (g : C(ℂ, ℝ)) (hg : ∀ z ∈ closedRibbon, g (P z) = z.re)
    (hg0 : g (γ 0) = 0) (k : ℝ) (hk : 1 ≤ k)
    (hpref : () ∈ GoodRibbonPrefix (fun _ : Unit => γ)
      (fun _ => firstFrontTime (fun t => g (γ t)) k) P ε)
    (hupper : LipschitzOnWith C P (ribbonStepPatch k))
    (hlower : ∀ z ∈ ribbonStepPatch k, ∀ w ∈ ribbonStepPatch k,
      dist z w ≤ L * dist (P z) (P w)) :
    ∃ d : RibbonHistory C L ε, d.U = U ∧ d.trace = γ ∧ d.forward = G ∧
      d.inverse = F ∧ d.chart = P ∧ d.front = k ∧
      (d.time : WithTop ℝ≥0) = firstFrontTime (fun t => g (γ t)) k := by
  let τ := firstFrontTime (fun t => g (γ t)) k
  have hfinite : τ ≠ ⊤ := hpref.1
  lift τ to ℝ≥0 using hfinite with T hT
  have hfirst : firstFrontTime (fun t => g (γ t)) k = (T : WithTop ℝ≥0) := hT.symm
  have hprefix : MapsTo γ (Icc 0 T) (ribbonCore P ε) := by
    simpa only [hfirst, WithTop.untopD_coe] using hpref.2.1
  have hend : γ T ∈ ribbonCore P (ε / 4) := by
    simpa only [hfirst, WithTop.untopD_coe] using hpref.2.2
  have hoff : |(coordinateInverse P closedRibbon (γ T)).im| ≤ ε / 4 := by
    obtain ⟨z, ⟨hz, hiε⟩, he⟩ := hend
    simpa only [← he, coordinateInverse_left hi hz] using hiε
  obtain ⟨d, hU', hγ', hG', hF', hP', hk', ht⟩ := actual_history_at_global_front
    U γ G F hU hw P hemb hP hi hH hescape g hg hg0 k hk T hfirst hprefix hoff hupper hlower
  exact ⟨d, hU', hγ', hG', hF', hP', hk', by rw [ht]; exact hfirst.symm⟩

/-- The uniform step's mass is charged to the actual successive global
fronts, and its continuation is again a good measurable physical prefix. -/
theorem RibbonHistory.actual_step_success
    {C L : ℝ≥0} {ε : ℝ} (d : RibbonHistory C L ε)
    (hε : ε ≤ 1 / 8) (hL : 0 < L) (κ v c : ℝ)
    (g : C(ℂ, ℝ)) (hg : ∀ z ∈ closedRibbon, g (d.chart z) = z.re)
    (hstep : d.futureTrace ∈ d.stepEvent κ v c)
    (hupper : LipschitzOnWith C d.chart (ribbonStepPatch (d.front + 1)))
    (hlower : ∀ u ∈ ribbonStepPatch (d.front + 1),
      ∀ v ∈ ribbonStepPatch (d.front + 1), dist u v ≤ L * dist (d.chart u) (d.chart v)) :
    () ∈ RibbonStepSuccess (fun _ : Unit => d.trace)
      (fun _ => firstFrontTime (fun t => g (d.trace t)) d.front)
      (fun _ => firstFrontTime (fun t => g (d.trace t)) (d.front + 1))
      d.chart ε κ v c (physicalMiddleRegion d.chart closedRibbon d.front ε) := by
  obtain ⟨d', hf, ht, hchart, _, htrace, _, _, _⟩ :=
    d.next_history_of_stepEvent hε hL κ v c hstep hupper hlower
  have hnext := d'.global_frontStop_eq g (by rw [hchart]; exact hg)
  rw [htrace, hf] at hnext
  have hprev := d.global_frontStop_eq g hg
  change _ ∧ _
  constructor
  · have hh := d'.goodRibbonPrefix
    simpa only [GoodRibbonPrefix, mem_ofPred_eq, htrace, hchart, hnext,
      WithTop.untopD_coe] using hh
  · have hm : ENNReal.ofReal c ≤ segmentSausageCharge κ d.futureTrace 0
        (frontTime (fun t => longitudinalCoordinate d.chart closedRibbon d.front
          (d.futureTrace t)) 1) v (physicalMiddleRegion d.chart closedRibbon d.front ε) := hstep.2
    change ENNReal.ofReal c ≤ segmentSausageCharge κ
      (fun t => d.trace (d.time + t)) 0 _ v _ at hm
    rw [segmentSausageCharge_shift, ← ht] at hm
    simpa only [mem_ofPred_eq, hprev, hnext, WithTop.untopD_coe] using hm

end SLEExactGauge

end

end OAI
