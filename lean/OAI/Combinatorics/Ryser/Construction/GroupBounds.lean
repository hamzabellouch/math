import OAI.Combinatorics.Ryser.Construction.GroupPlacement
import OAI.Combinatorics.Ryser.Geometry.Cardinality
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [instDecidableEqk : DecidableEq k] [instDecidableEqF : DecidableEq F] [Fintype k]

theorem exists_distinct_nonzero (hcard : 2 < Fintype.card k) :
    ∃ u v : k, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v := by
  classical
  have hex : ∃ v : k, v ≠ 0 ∧ v ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset k) ⊆ {0, 1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have hc := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_univ] at hc
    omega
  obtain ⟨v, hv0, hv1⟩ := hex
  exact ⟨1, v, one_ne_zero, hv0, hv1.symm⟩

theorem groupAxes_some_one_subset_none (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    groupAxes σ u v huv (some 1) ⊆ groupAltered σ u v huv none := by
  simpa [groupAxes, groupAltered, groupPlacement, cosetPlacement] using
    diagonal_one_axisDirections_subset_extra_alteredDirections σ u v huv hu hv

theorem groupAxes_none_subset_some_one (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    groupAxes σ u v huv none ⊆ groupAltered σ u v huv (some 1) := by
  simpa [groupAxes, groupAltered, groupPlacement, cosetPlacement] using
    extra_axisDirections_subset_diagonal_one_alteredDirections σ u v huv hu hv

theorem shared_groupAltered_axes_subset (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hu : u ≠ 0) (hv : v ≠ 0) {i j : ConfigurationGroup σ} {d : Direction F}
    (hij : i ≠ j) (hi : d ∈ groupAltered σ u v huv i)
    (hj : d ∈ groupAltered σ u v huv j) :
    groupAxes σ u v huv i ⊆ groupAltered σ u v huv j := by
  rcases shared_groupAltered σ u v huv hij hi hj with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact groupAxes_none_subset_some_one σ u v huv hu hv
  · rcases h with ⟨rfl, rfl⟩
    exact groupAxes_some_one_subset_none σ u v huv hu hv

theorem groupConflict_card_le (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) :
    (groupConflict σ u v huv i).card ≤ Fintype.card k + 1 := by
  classical
  cases i with
  | none => exact le_of_eq (embeddedDirections_card σ)
  | some c =>
      by_cases hc : c = 1
      · simpa [groupConflict, hc] using le_of_eq (embeddedDirections_card σ)
      · simp only [groupConflict, ite_eq_right hc, groupAltered_card]
        omega

def groupPoints (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : Finset (Point F) :=
  Finset.univ.image (fun w : Point k => (groupPlacement σ u v huv i).apply (mapPoint σ w))

theorem groupPoints_card (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) :
    (groupPoints σ u v huv i).card = Fintype.card k ^ 2 := by
  have hinj : Function.Injective
      (fun w : Point k => (groupPlacement σ u v huv i).apply (mapPoint σ w)) :=
    (groupPlacement σ u v huv i).apply_injective.comp (mapPoint_injective σ)
  rw [groupPoints, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  exact card_point

section FiniteAmbient

variable [Fintype F]

theorem card_groups_mul_sub_one_le (σ : k →+* F) :
    Fintype.card (ConfigurationGroup σ) * (Fintype.card k - 1) ≤
      2 * Fintype.card F := let _ := instDecidableEqk; let _ := instDecidableEqF; by
  have hcard : Fintype.card k ≤ Fintype.card F :=
    Fintype.card_le_of_injective σ σ.injective
  rw [card_configurationGroup, Nat.add_mul, card_cosetIndex_mul, one_mul]
  omega

end FiniteAmbient

end RyserCoveringCounterexample.Construction

end

end OAI
