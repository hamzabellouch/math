import OAI.Analysis.FiniteFactor.Fiber.PairZeroSet
import OAI.Analysis.FiniteFactor.CrossedProduct.LusinCompact

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

def sourceCappedRatio (θ : SourceCoordinate → ℝ) (z : SourceTorus × SourceTorus) (k : ℤ) : ℂ :=
  (min (sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.2) /
    sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.1)) 1 : ℝ)

theorem sourceCappedRatio_norm (θ : SourceCoordinate → ℝ) (z : SourceTorus × SourceTorus) (k : ℤ) :
    ‖sourceCappedRatio θ z k‖ ≤ 1 := by
  rw [sourceCappedRatio, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_min (le_of_lt (div_pos (sourceCocycle_pos ..) (sourceCocycle_pos ..))) zero_le_one)]
  exact min_le_right _ _

theorem sourceCappedRatio_measurable (θ : SourceCoordinate → ℝ) (k : ℤ) :
    Measurable (fun z => sourceCappedRatio θ z k) := by
  apply Complex.measurable_ofReal.comp
  apply Measurable.min _ measurable_const
  exact (((sourceCocycle_measurable θ sourceLogWeight k).comp
    sourceTorusRepresentative_preserving.measurable).comp measurable_snd).div
    (((sourceCocycle_measurable θ sourceLogWeight k).comp
      sourceTorusRepresentative_preserving.measurable).comp measurable_fst)

theorem sourceCappedRatio_continuousOn (θ : SourceCoordinate → ℝ) (Q : Set SourceTorus)
    (hF : ∀ k : ℤ, ContinuousOn
      (fun z => sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z)) Q) (k : ℤ) :
    ContinuousOn (fun z => sourceCappedRatio θ z k) (Q ×ˢ Q) := by
  apply Complex.continuous_ofReal.comp_continuousOn
  apply ContinuousOn.inf _ continuousOn_const
  exact ((hF k).comp continuous_snd.continuousOn (fun z hz => hz.2)).div
    ((hF k).comp continuous_fst.continuousOn (fun z hz => hz.1))
    (fun z _ => ne_of_gt (sourceCocycle_pos ..))

/-- The capped equation uses the previously constructed field of the original
operator, on the actual sampling torus. -/
def sourceCappedPairZeroSet (θ : SourceCoordinate → ℝ)
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    Set (SourceTorus × SourceTorus) :=
  {z | fiberPairResidual (sourceTorusOperatorField H) (sourceCappedRatio θ)
    (sourceCappedRatio_norm θ) z = 0}

theorem sourceCappedPairZeroSet_measurable (θ : SourceCoordinate → ℝ)
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    MeasurableSet (sourceCappedPairZeroSet θ H) :=
  fiberPairZeroSet_measurable _ _ _ (sourceTorusOperatorField_stronglyMeasurable H)
    (sourceCappedRatio_measurable θ)

/-- The compact zero sets needed for Portmanteau are constructed from the
actual field and original cocycles, with arbitrarily small Haar loss. -/
theorem exists_source_capped_compact (θ : SourceCoordinate → ℝ)
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    {s : Set SourceTorus} (hs : MeasurableSet s) (hfull : ∀ᵐ z ∂sourceTorusHaar, z ∈ s)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ Q, Q ⊆ s ∧ IsCompact Q ∧ sourceTorusHaar Qᶜ < ε ∧
      IsCompact ((Q ×ˢ Q) ∩ sourceCappedPairZeroSet θ H) := by
  obtain ⟨Q,hQs,hQ,hμQ,hF,hP⟩ := exists_source_lusin_compact θ H hs hfull hε
  exact ⟨Q,hQs,hQ,hμQ,fiberPairZeroSet_compact _ _ _ Q hQ ‖H‖
    (fun z _ => sourceTorusOperatorField_norm H z) hP
      (sourceCappedRatio_continuousOn θ Q hF)⟩

end
end FiniteFactor

end OAI
