import OAI.Analysis.FiniteFactor.CrossedProduct.TorusOperatorField
import OAI.Analysis.FiniteFactor.CrossedProduct.FiberSeparable
import OAI.Analysis.FiniteFactor.CompactGraphLusin

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- All cocycles and all vector columns of the actual operator field are
continuous on one compact subset of any prescribed Borel conull set. -/
theorem exists_source_lusin_compact (θ : SourceCoordinate → ℝ)
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    {s : Set SourceTorus} (hs : MeasurableSet s) (hfull : ∀ᵐ z ∂sourceTorusHaar, z ∈ s)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ Q, Q ⊆ s ∧ IsCompact Q ∧ sourceTorusHaar Qᶜ < ε ∧
      (∀ k : ℤ, ContinuousOn
        (fun z => sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z)) Q) ∧
      (∀ k : ℤ, ContinuousOn
        (fun z => sourceTorusOperatorField H z (lp.single 2 k (1 : ℂ))) Q) := by
  borelize (↥SourceFiberHilbert)
  let f : SourceTorus → (ℤ → ℝ × SourceFiberHilbert) := fun z k =>
    (sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z),
      sourceTorusOperatorField H z (lp.single 2 k (1 : ℂ)))
  have hf : Measurable f := by
    apply Measurable.of_eval
    intro k
    exact ((sourceCocycle_measurable θ sourceLogWeight k).comp
      sourceTorusRepresentative_preserving.measurable).prodMk
        (sourceTorusOperatorField_stronglyMeasurable H (lp.single 2 k (1 : ℂ))).measurable
  obtain ⟨Q,hQs,hQ,hμQ,hfQ⟩ := exists_compact_lusin sourceTorusHaar hf hs hfull hε
  refine ⟨Q,hQs,hQ,hμQ,?_,?_⟩
  · intro k
    exact continuous_fst.comp_continuousOn ((continuous_apply k).comp_continuousOn hfQ)
  · intro k
    exact continuous_snd.comp_continuousOn ((continuous_apply k).comp_continuousOn hfQ)

end
end FiniteFactor

end OAI
