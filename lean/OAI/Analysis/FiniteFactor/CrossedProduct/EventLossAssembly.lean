import OAI.Analysis.FiniteFactor.CrossedProduct.CurrentTaggedEvent
import OAI.Analysis.FiniteFactor.CrossedProduct.FutureBoundaryLoss
import OAI.Analysis.FiniteFactor.CrossedProduct.DiagonalLoss

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Current and future exclusions together give exactly the source boundary. -/
theorem sourceCurrentFuture_boundary (j : ℕ) (ω : SourceBiasedSample)
    (hc : ω ∈ sourceCurrentTaggedEvent j) (hf : ω ∈ sourceFutureBoundaryEvent j) :
    ω ∈ sourceBoundaryEvent j := by
  intro i hi
  rcases i with ⟨s,i⟩
  change j ≤ s at hi
  by_cases h : s = j
  · subst s
    rw [sourceExclusionWidth_current]
    exact hc.2 i
  · have hjs : j+1 ≤ s := by omega
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hjs
    exact sourceFutureBoundary_no_bad j ω hf n i

def sourceDiagonalLossSet
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (j : ℕ) (b : Bool) : Set SourceBiasedSample :=
  {ω | (if b then 1-(sourceCentralCoefficient p (sourceBiasedEndpoint (fun _ => true) ω)).re
    else (sourceCentralCoefficient p (sourceBiasedEndpoint (fun _ => false) ω)).re) < 1/((j : ℝ)+1)}

/-- No independence is used between the current block and the three losses. -/
theorem sourceProjectionEvent_mass_losses
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (j : ℕ) :
    Real.exp (-82) ≤ (sourceBiasedLaw j).real (sourceProjectionEvent p j) +
      (sourceBiasedLaw j).real (sourceFutureBoundaryEvent j)ᶜ +
      (sourceBiasedLaw j).real (sourceDiagonalLossSet p j false) +
      (sourceBiasedLaw j).real (sourceDiagonalLossSet p j true) := by
  have hsub : sourceCurrentTaggedEvent j ⊆
      ((sourceProjectionEvent p j ∪ (sourceFutureBoundaryEvent j)ᶜ) ∪ sourceDiagonalLossSet p j false) ∪
        sourceDiagonalLossSet p j true := by
    intro ω hc
    by_cases hf : ω ∈ sourceFutureBoundaryEvent j
    · by_cases hx : ω ∈ sourceDiagonalLossSet p j false
      · exact Or.inl (Or.inr hx)
      · by_cases hy : ω ∈ sourceDiagonalLossSet p j true
        · exact Or.inr hy
        · refine Or.inl (Or.inl (Or.inl ⟨⟨hc.1,sourceCurrentFuture_boundary j ω hc hf⟩,?_⟩))
          constructor
          · exact le_of_not_gt hx
          · exact le_of_not_gt hy
    · exact Or.inl (Or.inl (Or.inr hf))
  have hlow : Real.exp (-82) ≤ (sourceBiasedLaw j).real (sourceCurrentTaggedEvent j) := by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) (sourceCurrentTaggedEvent_mass j)
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le,measureReal_def] using hh
  apply hlow.trans ((measureReal_mono hsub).trans ?_)
  apply (measureReal_union_le _ _).trans
  apply add_le_add _ le_rfl
  apply (measureReal_union_le _ _).trans
  exact add_le_add (measureReal_union_le _ _) le_rfl

end
end FiniteFactor

end OAI
