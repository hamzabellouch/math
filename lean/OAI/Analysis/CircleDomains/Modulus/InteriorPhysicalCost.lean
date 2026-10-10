import OAI.Analysis.CircleDomains.Modulus.JoinedPhysicalCost
import OAI.Analysis.CircleDomains.Probability.ReversedPhysicalOccupation
import OAI.Analysis.CircleDomains.Selection.LastEntryCuts

namespace OAI

/-! Interior cost, full fragment cost, and the endpoint convention for a
one-ended path are related without losing or duplicating a dust toll. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] [BorelSpace X] in
theorem interiorPhysicalTollCost_le_full (d : PathCodeData X Y)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (γ : FinitePhysicalPath d.domainEquiv d.basePoint) :
    interiorPhysicalTollCost d g m γ ≤ physicalTollCost d g m γ := by
  unfold interiorPhysicalTollCost physicalTollCost
  apply add_le_add le_rfl
  rw [boundaryToll_eq_timeToll]
  exact timeToll_mono γ.val m (subset_univ _)

omit [MeasurableSpace X] [BorelSpace X] in
theorem interiorPhysicalTollCost_eq_full (d : PathCodeData X Y)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hzero : m (γ.val ⊥) = 0) (hone : m (γ.val ⊤) = 0) :
    interiorPhysicalTollCost (X := X) (Y := Y) d g m γ = physicalTollCost d g m γ := by
  unfold interiorPhysicalTollCost physicalTollCost
  rw [timeToll_eq_interior_of_zero_endpoints γ.val m hzero hone]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace C(PathTime, X)] in
theorem preterminalToll_eq_interior_of_initial_zero
    (γ : C(PathTime, X)) (m : X → ℝ≥0∞) (hzero : m (γ ⊥) = 0) :
    preterminalToll γ m = timeToll γ (Ioo (⊥ : PathTime) ⊤) m := by
  rw [preterminalToll_eq_timeToll]
  apply timeToll_eq_of_zero_difference
  · exact fun _ h => h.2
  · intro t ht
    have he : t = ⊥ := by
      by_contra hn
      exact ht.2 ⟨bot_lt_iff_ne_bot.mpr hn, ht.1⟩
    exact he ▸ hzero

omit [MeasurableSpace X] [BorelSpace X] in
theorem interiorPhysicalTollCost_reversed (d : PathCodeData X Y)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (γ : FinitePhysicalPath d.domainEquiv d.basePoint) :
    interiorPhysicalTollCost (X := X) (Y := Y) d g m (reversedFinitePhysicalPath d.domainEquiv d.basePoint γ) =
      interiorPhysicalTollCost (X := X) (Y := Y) d g m γ := by
  unfold interiorPhysicalTollCost
  rw [dyadicPhysicalOccupation_reversed]
  exact congrArg _ (interiorToll_reversed γ.val m)


omit [BorelSpace X] in
theorem exists_allowed_reversed_interior_cost
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = Γ.1.val ⊤ ∧ ρ.val ⊤ = Γ.1.val ⊥ ∧
      interiorPhysicalTollCost (X := X) (Y := Y) d g m ρ = interiorPhysicalTollCost (X := X) (Y := Y) d g m Γ.1 := by
  refine ⟨reversedFinitePhysicalPath d.domainEquiv d.basePoint Γ.1,
    fun k => reversedTag (Γ.2 k), ?_, ?_, ?_, ?_⟩
  · exact allowedTaggedPath_reversed d ν N (Γ.1.val, Γ.2) hΓ hpoint
  · exact reversedPath_zero Γ.1.val
  · exact reversedPath_one Γ.1.val
  · exact interiorPhysicalTollCost_reversed d g m Γ.1

end CircleDomainRigidity

end

end OAI
