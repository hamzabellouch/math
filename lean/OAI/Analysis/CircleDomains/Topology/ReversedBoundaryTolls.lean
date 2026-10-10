import OAI.Analysis.CircleDomains.Selection.ReversedTags
import OAI.Analysis.CircleDomains.Topology.AffineBoundaryTolls

namespace OAI

/-! Dust tolls under reversal, including the two distinct endpoint
conventions used for collar fragments and one-ended paths. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem boundaryToll_reversed (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    boundaryToll (reversedPath γ) m = boundaryToll γ m := by
  exact unitInterval.symmHomeomorph.toEquiv.tsum_eq (fun t => m (γ t))

theorem preterminalToll_reversed_add_initial (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    preterminalToll (reversedPath γ) m + m (γ ⊥) =
      preterminalToll γ m + m (γ ⊤) := by
  have he : reversedPath γ ⊤ = γ ⊥ := by
    change γ (unitInterval.symm (1 : PathTime)) = γ (0 : PathTime)
    rw [unitInterval.symm_one]
  rw [← he, preterminalToll_add_terminal, boundaryToll_reversed,
    preterminalToll_add_terminal]

theorem preterminalToll_reversed_of_zero_endpoints (γ : C(PathTime, X)) (m : X → ℝ≥0∞)
    (hstart : m (γ ⊥) = 0) (hend : m (γ ⊤) = 0) :
    preterminalToll (reversedPath γ) m = preterminalToll γ m := by
  simpa only [hstart, hend, add_zero] using preterminalToll_reversed_add_initial γ m

theorem interiorToll_reversed (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    timeToll (reversedPath γ) (Ioo (⊥ : PathTime) ⊤) m =
      timeToll γ (Ioo (⊥ : PathTime) ⊤) m := by
  have hmap : ∀ s ∈ Ioo (⊥ : PathTime) ⊤, unitInterval.symm s ∈ Ioo (⊥ : PathTime) ⊤ := by
    intro s hs
    constructor
    · change (0 : ℝ) < 1 - (s : ℝ)
      exact sub_pos.mpr hs.2
    · change 1 - (s : ℝ) < (1 : ℝ)
      have hpos : (0 : ℝ) < s := hs.1
      linarith
  have he : unitInterval.symm '' Ioo (⊥ : PathTime) ⊤ = Ioo ⊥ ⊤ := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hmap s hs
    · intro ht
      refine ⟨unitInterval.symm t, ?_, unitInterval.symm_symm t⟩
      exact hmap t ht
  exact (timeToll_image γ unitInterval.symm unitInterval.symm_bijective.injective
    (Ioo (⊥ : PathTime) ⊤) m).symm.trans (congrArg (fun A => timeToll γ A m) he)

end CircleDomainRigidity

end

end OAI
