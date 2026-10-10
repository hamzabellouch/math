import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

open Set Filter MeasureTheory
open scoped Topology

namespace CompactFluxDifferentiation
variable {X E : Type*} [TopologicalSpace X] [compactSpaceX : CompactSpace X]
  [measurableSpaceX : MeasurableSpace X] [borelSpaceX : BorelSpace X] [secondCountableTopologyX : SecondCountableTopology X]
  [NormedAddCommGroup E] [normedSpaceRealE : NormedSpace ℝ E] [completeSpaceE : CompleteSpace E]
  {μ : Measure X} [IsFiniteMeasure μ]
  {F G : ℝ → X → E} {a b t : ℝ}

omit compactSpaceX measurableSpaceX borelSpaceX secondCountableTopologyX normedSpaceRealE completeSpaceE in
lemma continuous_slice [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [NormedSpace ℝ E] [CompleteSpace E] (hF : ContinuousOn (fun p : ℝ × X => F p.1 p.2)
    (Icc a b ×ˢ univ)) (ht : t ∈ Icc a b) : Continuous (F t) := by
  exact hF.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨ht, mem_univ x⟩)

lemma integrable_slice (hF : ContinuousOn (fun p : ℝ × X => F p.1 p.2)
    (Icc a b ×ˢ univ)) (ht : t ∈ Icc a b) : Integrable (F t) μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_slice hF ht).continuousOn
  exact Integrable.of_bound (continuous_slice hF ht).aestronglyMeasurable C
    (ae_of_all μ (fun x => hC x (mem_univ x)))

/-- Continuity includes both endpoints of the compact parameter interval. -/
theorem continuousOn_integral
    (hF : ContinuousOn (fun p : ℝ × X => F p.1 p.2) (Icc a b ×ˢ univ)) :
    ContinuousOn (fun s => ∫ x, F s x ∂μ) (Icc a b) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hF
  apply continuousOn_of_dominated (bound := fun _ => C)
  · intro s hs
    exact (continuous_slice hF hs).aestronglyMeasurable
  · intro s hs
    exact ae_of_all μ (fun x => hC (s,x) ⟨hs, mem_univ x⟩)
  · exact integrable_const C
  · apply ae_of_all
    intro x
    exact hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, mem_univ x⟩)

/-- The local compact-interval argument also gives continuity on the full line. -/
theorem continuous_integral
    (hF : Continuous (fun p : ℝ × X => F p.1 p.2)) :
    Continuous (fun s => ∫ x, F s x ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (continuousOn_integral (a := t-1) (b := t+1) hF.continuousOn).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

/-- Joint continuity on a compact parameter interval and compact finite-measure
fiber supplies every domination and measurability obligation. -/
theorem hasDerivAt_integral
    (hF : ContinuousOn (fun p : ℝ × X => F p.1 p.2) (Icc a b ×ˢ univ))
    (hG : ContinuousOn (fun p : ℝ × X => G p.1 p.2) (Icc a b ×ˢ univ))
    (hd : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r => F r x) (G s x) s)
    (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, G t x ∂μ) t := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hG
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := G) (s := Ioo a b) (bound := fun _ => C)
    (Ioo_mem_nhds ht.1 ht.2) ?_ (integrable_slice hF ⟨ht.1.le, ht.2.le⟩)
    (continuous_slice hG ⟨ht.1.le, ht.2.le⟩).aestronglyMeasurable ?_
    (integrable_const C) ?_).2
  · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (continuous_slice hF ⟨hs.1.le, hs.2.le⟩).aestronglyMeasurable
  · exact ae_of_all μ (fun x s hs => hC (s,x) ⟨⟨hs.1.le, hs.2.le⟩, mem_univ x⟩)
  · exact ae_of_all μ (fun x s hs => hd s hs x)

end CompactFluxDifferentiation

end OAI
