import OAI.Combinatorics.Ryser.Construction.DirectionPlacement
import Mathlib.Data.Fintype.Card

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [instFintypek : Fintype k]

def alteredDirections (σ : k →+* F) (M : PlaneLinearMap F) : Finset (Direction F) :=
  (Finset.univ.erase 0).image (fun t : k => placedDirection σ M (some t))

def axisDirections (σ : k →+* F) (M : PlaneLinearMap F) : Finset (Direction F) :=
  ({none, some 0} : Finset (Direction k)).image (placedDirection σ M)

theorem mem_alteredDirections_iff (σ : k →+* F) (M : PlaneLinearMap F)
    (d : Direction F) :
    d ∈ alteredDirections σ M ↔
      ∃ t : k, t ≠ 0 ∧ placedDirection σ M (some t) = d := by
  simp only [alteredDirections, Finset.mem_image, Finset.mem_erase,
    Finset.mem_univ, and_true]

theorem mem_axisDirections_iff (σ : k →+* F) (M : PlaneLinearMap F)
    (d : Direction F) :
    d ∈ axisDirections σ M ↔
      d = placedDirection σ M none ∨ d = placedDirection σ M (some 0) := let _ := instFintypek; by
  simp [axisDirections]

theorem placedDirection_mem_alteredDirections (σ : k →+* F) (M : PlaneLinearMap F)
    (t : k) (ht : t ≠ 0) :
    placedDirection σ M (some t) ∈ alteredDirections σ M :=
  (mem_alteredDirections_iff σ M _).mpr ⟨t, ht, rfl⟩

theorem alteredDirections_nonempty (σ : k →+* F) (M : PlaneLinearMap F) :
    (alteredDirections σ M).Nonempty :=
  ⟨placedDirection σ M (some 1),
    placedDirection_mem_alteredDirections σ M 1 one_ne_zero⟩

theorem disjoint_alteredDirections_axisDirections (σ : k →+* F)
    (M : PlaneLinearMap F) : Disjoint (alteredDirections σ M) (axisDirections σ M) := by
  apply Finset.disjoint_left.mpr
  intro d hd ha
  obtain ⟨t, ht, rfl⟩ := (mem_alteredDirections_iff σ M d).mp hd
  rcases (mem_axisDirections_iff σ M _).mp ha with hnone | hzero
  · have h := placedDirection_injective σ M hnone
    cases h
  · exact ht (Option.some.inj (placedDirection_injective σ M hzero))

theorem placedDirection_axis_notMem_alteredDirections (σ : k →+* F)
    (M : PlaneLinearMap F) (d : Direction k) (haxis : d = none ∨ d = some 0) :
    placedDirection σ M d ∉ alteredDirections σ M := by
  have ha : placedDirection σ M d ∈ axisDirections σ M := by
    apply (mem_axisDirections_iff σ M _).mpr
    rcases haxis with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  intro hd
  exact Finset.disjoint_left.mp (disjoint_alteredDirections_axisDirections σ M) hd ha

theorem placedDirection_mem_altered_or_axis (σ : k →+* F) (M : PlaneLinearMap F)
    (d : Direction k) :
    placedDirection σ M d ∈ alteredDirections σ M ∪ axisDirections σ M := by
  cases d with
  | none =>
      exact Finset.mem_union_right _ ((mem_axisDirections_iff σ M _).mpr (Or.inl rfl))
  | some t =>
      by_cases ht : t = 0
      · subst t
        exact Finset.mem_union_right _ ((mem_axisDirections_iff σ M _).mpr (Or.inr rfl))
      · exact Finset.mem_union_left _ (placedDirection_mem_alteredDirections σ M t ht)

theorem card_alteredDirections (σ : k →+* F) (M : PlaneLinearMap F) :
    (alteredDirections σ M).card = Fintype.card k - 1 := by
  have hinj : Function.Injective (fun t : k => placedDirection σ M (some t)) := by
    intro t u h
    exact Option.some.inj (placedDirection_injective σ M h)
  unfold alteredDirections
  rw [Finset.card_image_of_injective _ hinj,
    Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]

theorem card_axisDirections (σ : k →+* F) (M : PlaneLinearMap F) :
    (axisDirections σ M).card = 2 := let _ := instFintypek; by
  unfold axisDirections
  rw [Finset.card_image_of_injective _ (placedDirection_injective σ M)]
  simp

theorem existsUnique_alteredSlope (σ : k →+* F) (M : PlaneLinearMap F)
    (d : {d : Direction F // d ∈ alteredDirections σ M}) :
    ∃! t : k, t ≠ 0 ∧ placedDirection σ M (some t) = d.val := by
  obtain ⟨t, ht, htd⟩ := (mem_alteredDirections_iff σ M d.val).mp d.property
  refine ⟨t, ⟨ht, htd⟩, ?_⟩
  intro u hu
  exact Option.some.inj (placedDirection_injective σ M (hu.2.trans htd.symm))

noncomputable def alteredInverseSlope (σ : k →+* F) (M : PlaneLinearMap F)
    (d : {d : Direction F // d ∈ alteredDirections σ M}) : k :=
  Classical.choose (existsUnique_alteredSlope σ M d).exists

theorem alteredInverseSlope_spec (σ : k →+* F) (M : PlaneLinearMap F)
    (d : {d : Direction F // d ∈ alteredDirections σ M}) :
    alteredInverseSlope σ M d ≠ 0 ∧
      placedDirection σ M (some (alteredInverseSlope σ M d)) = d.val :=
  Classical.choose_spec (existsUnique_alteredSlope σ M d).exists

theorem alteredInverseSlope_ne_zero (σ : k →+* F) (M : PlaneLinearMap F)
    (d : {d : Direction F // d ∈ alteredDirections σ M}) :
    alteredInverseSlope σ M d ≠ 0 :=
  (alteredInverseSlope_spec σ M d).1

theorem placedDirection_inverseSlope (σ : k →+* F) (M : PlaneLinearMap F)
    (d : {d : Direction F // d ∈ alteredDirections σ M}) :
    placedDirection σ M (some (alteredInverseSlope σ M d)) = d.val :=
  (alteredInverseSlope_spec σ M d).2

theorem inverseSlope_placedDirection (σ : k →+* F) (M : PlaneLinearMap F)
    (t : k) (ht : t ≠ 0) :
    alteredInverseSlope σ M
      ⟨placedDirection σ M (some t), placedDirection_mem_alteredDirections σ M t ht⟩ = t := by
  apply Option.some.inj
  apply placedDirection_injective σ M
  exact placedDirection_inverseSlope σ M
    ⟨placedDirection σ M (some t), placedDirection_mem_alteredDirections σ M t ht⟩

end RyserCoveringCounterexample.Construction

end OAI
