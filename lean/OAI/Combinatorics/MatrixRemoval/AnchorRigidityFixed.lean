import OAI.Combinatorics.MatrixRemoval.AnchorProperties
import OAI.Combinatorics.MatrixRemoval.AnchorRigidity

namespace OAI

universe uT

namespace Problem348.AnchorRigidity

/-- The actual first 32 positions of the fixed anchor. -/
def firstCore : Finset (Fin 64) := Finset.univ.filter fun i => i.val < 32

@[simp] theorem mem_firstCore (i : Fin 64) : i ∈ firstCore ↔ i.val < 32 := by
  simp [firstCore]

theorem firstCore_card : firstCore.card = 32 := by decide

theorem firstCore_column_zeros (j : Fin 64) :
    (firstCore.filter fun i => anchor64 i j = false).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi k hk
  obtain ⟨hic, hij⟩ := Finset.mem_filter.mp hi
  obtain ⟨hkc, hkj⟩ := Finset.mem_filter.mp hk
  exact ((anchor64_first32_zero_iff i j ((mem_firstCore i).mp hic)).mp hij).trans
    ((anchor64_first32_zero_iff k j ((mem_firstCore k).mp hkc)).mp hkj).symm

theorem firstCore_row_zeros (i : Fin 64) :
    (firstCore.filter fun j => anchor64 i j = false).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro j hj k hk
  obtain ⟨hjc, hij⟩ := Finset.mem_filter.mp hj
  obtain ⟨hkc, hik⟩ := Finset.mem_filter.mp hk
  exact ((anchor64_first32_column_zero_iff i j ((mem_firstCore j).mp hjc)).mp hij).symm.trans
    ((anchor64_first32_column_zero_iff i k ((mem_firstCore k).mp hkc)).mp hik)

/-- A majority of anchor labels in an initial segment contains the dense prefix.
This is the small order/cardinality bridge from the no-shattering majority
argument to the finite rigidity theorem. -/
theorem prefix_of_majority {T : Type uT} (mode : Fin 64 → Option T)
    (initial : ∀ i j, i ≤ j → mode j ≠ none → mode i ≠ none)
    (majority : 32 < (Finset.univ.filter fun i => (mode i).isSome).card) :
    ∀ i : Fin 64, i.val < 32 → ∃ t, mode i = some t := by
  intro i hi
  cases hmi : mode i with
  | some t => exact ⟨t, rfl⟩
  | none =>
    have hsub : (Finset.univ.filter fun j => (mode j).isSome) ⊆ Finset.Iio i := by
      intro j hj
      have hjs := (Finset.mem_filter.mp hj).2
      have hjn : mode j ≠ none := by
        intro hnone
        simp [hnone] at hjs
      apply Finset.mem_Iio.mpr
      by_contra hnot
      exact initial i j (le_of_not_gt hnot) hjn hmi
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega

/-- The majority conclusion on either axis provides the prefix alternative
required by `anchor64_rigidity_of_prefix`. -/
theorem prefix_alternative_of_majority {T : Type uT}
    (rowMode colMode : Fin 64 → Option T)
    (row_initial : ∀ i j, i ≤ j → rowMode j ≠ none → rowMode i ≠ none)
    (col_initial : ∀ i j, i ≤ j → colMode j ≠ none → colMode i ≠ none)
    (majority : 32 < (Finset.univ.filter fun i => (rowMode i).isSome).card ∨
      32 < (Finset.univ.filter fun j => (colMode j).isSome).card) :
    (∀ i : Fin 64, i.val < 32 → ∃ t, rowMode i = some t) ∨
      (∀ j : Fin 64, j.val < 32 → ∃ t, colMode j = some t) := by
  exact majority.imp (prefix_of_majority rowMode row_initial)
    (prefix_of_majority colMode col_initial)

/-- Same-mode conclusion for the exact anchor after prefix pinning. -/
theorem anchor64_rigidity_of_prefix {T : Type uT}
    (rowMode colMode : Fin 64 → Option T)
    (dummyRow dummyCol : Fin 64 → Prop)
    (hprefix : (∀ i : Fin 64, i.val < 32 → ∃ t, rowMode i = some t) ∨
      (∀ j : Fin 64, j.val < 32 → ∃ t, colMode j = some t))
    (variable_col_sparse : ∀ j, colMode j = none → ¬ dummyCol j →
      (∀ i ∈ firstCore, ∃ t, rowMode i = some t) →
      (firstCore.filter fun i => anchor64 i j = true).card ≤ 4)
    (variable_row_sparse : ∀ i, rowMode i = none → ¬ dummyRow i →
      (∀ j ∈ firstCore, ∃ t, colMode j = some t) →
      (firstCore.filter fun j => anchor64 i j = true).card ≤ 4)
    (dummy_row_unique : ∀ i k, dummyRow i → dummyRow k → i = k)
    (dummy_col_unique : ∀ j k, dummyCol j → dummyCol k → j = k)
    (cross_mode : ∀ i j t u, rowMode i = some t → colMode j = some u →
      anchor64 i j = true → t = u)
    (nonanchor_row_unit : ∀ i, rowMode i = none → ∀ j k t,
      colMode j = some t → colMode k = some t →
      anchor64 i j = true → anchor64 i k = true → j = k)
    (nonanchor_col_unit : ∀ j, colMode j = none → ∀ i k t,
      rowMode i = some t → rowMode k = some t →
      anchor64 i j = true → anchor64 k j = true → i = k) :
    ∃ t, (∀ i, rowMode i = some t) ∧ (∀ j, colMode j = some t) := by
  apply rigidity anchor64 rowMode colMode dummyRow dummyCol
    (dummy_row_unique := dummy_row_unique) (dummy_col_unique := dummy_col_unique)
    (cross_mode := cross_mode) (nonanchor_row_unit := nonanchor_row_unit)
    (nonanchor_col_unit := nonanchor_col_unit)
  · rcases hprefix with hr | hc
    · left
      have ha : ∀ i ∈ firstCore, ∃ t, rowMode i = some t :=
        fun i hi => hr i ((mem_firstCore i).mp hi)
      exact ⟨firstCore, by rw [firstCore_card]; omega, ha,
        firstCore_column_zeros, fun j hj hd => variable_col_sparse j hj hd ha⟩
    · right
      have ha : ∀ j ∈ firstCore, ∃ t, colMode j = some t :=
        fun j hj => hc j ((mem_firstCore j).mp hj)
      exact ⟨firstCore, by rw [firstCore_card]; omega, ha,
        firstCore_row_zeros, fun i hi hd => variable_row_sparse i hi hd ha⟩
  · intro i
    exact (by omega : 2 ≤ 58).trans (anchor64_row_ones i)
  · intro j
    exact (by omega : 2 ≤ 48).trans (anchor64_column_ones j)

end Problem348.AnchorRigidity

end OAI
