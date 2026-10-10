import Mathlib

namespace OAI

section

open Set Cardinal

namespace InfiniteMatroidCounterexample

abbrev CIndex := Cardinal.continuum.{0}.ord.ToType

lemma cindex_card : Cardinal.mk CIndex = Cardinal.continuum := Cardinal.mk_ord_toType _

lemma cindex_initial : (Cardinal.mk CIndex).ord = Ordinal.type ((· < ·) : CIndex → CIndex → Prop) := by
  rw [cindex_card, Ordinal.type_toType]

lemma cindex_predecessors (i : CIndex) : Cardinal.mk (Iio i) < Cardinal.continuum := by
  simpa only [cindex_card] using Cardinal.mk_Iio_lt i cindex_initial

lemma cindex_initial_segment (i : CIndex) : Cardinal.mk (Iic i) < Cardinal.continuum := by
  have h : Iic i = insert i (Iio i) := by ext x; simp [le_iff_lt_or_eq, eq_comm, or_comm]
  rw [h]
  apply lt_of_le_of_lt Cardinal.mk_insert_le
  have h0 := cindex_predecessors i
  have hc : ℵ₀ < Cardinal.continuum := Cardinal.aleph0_lt_continuum
  calc
    _ ≤ max (Cardinal.mk (Iio i)) ℵ₀ + max (Cardinal.mk (Iio i)) ℵ₀ :=
      add_le_add (le_max_left _ _) (le_trans Cardinal.one_le_aleph0 (le_max_right _ _))
    _ = max (Cardinal.mk (Iio i)) ℵ₀ := Cardinal.add_eq_self (le_max_right _ _)
    _ < Cardinal.continuum := max_lt h0 hc

/-- Cardinal arithmetic used at each stage; it does not assert regularity of the continuum. -/
lemma finite_union_small {α ι : Type} (hι : Cardinal.mk ι < Cardinal.continuum)
    (F : ι → Set α) (hF : ∀ i, (F i).Finite) :
    Cardinal.mk (⋃ i, F i) < Cardinal.continuum := by
  calc
    Cardinal.mk (⋃ i, F i) ≤ Cardinal.mk ι * ⨆ i, Cardinal.mk (F i) := Cardinal.mk_iUnion_le F
    _ ≤ max (Cardinal.mk ι) ℵ₀ * max (Cardinal.mk ι) ℵ₀ := by
      apply mul_le_mul' (le_max_left _ _)
      apply ciSup_le'
      intro i
      let := (hF i).fintype
      exact (Cardinal.lt_aleph0_of_finite (F i)).le.trans (le_max_right _ _)
    _ = max (Cardinal.mk ι) ℵ₀ := Cardinal.mul_eq_self (le_max_right _ _)
    _ < Cardinal.continuum := max_lt hι Cardinal.aleph0_lt_continuum

lemma exists_avoid_finite_family {ι : Type} (hι : Cardinal.mk ι < Cardinal.continuum)
    (F : ι → Set CIndex) (hF : ∀ i, (F i).Finite) :
    ∃ t : CIndex, ∀ i, t ∉ F i := by
  have hcard := finite_union_small hι F hF
  have hn : (⋃ i, F i) ≠ Set.univ := by
    intro heq
    rw [heq, Cardinal.mk_univ, cindex_card] at hcard
    exact lt_irrefl _ hcard
  obtain ⟨t, ht⟩ := (Set.ne_univ_iff_exists_notMem _).mp hn
  exact ⟨t, fun i hi ↦ ht (mem_iUnion.mpr ⟨i, hi⟩)⟩

lemma binary_card : Cardinal.mk (ℕ → Bool) = Cardinal.continuum := by
  rw [Cardinal.mk_arrow]
  simp only [Cardinal.mk_fintype, Fintype.card_bool, Cardinal.mk_nat, Cardinal.lift_id, Nat.cast_ofNat]
  exact Cardinal.two_power_aleph0

noncomputable def cindexBinaryEquiv : CIndex ≃ (ℕ → Bool) :=
  Classical.choice (Cardinal.eq.mp (cindex_card.trans binary_card.symm))

/-- Enumeration of all subsets of any countably infinite type, on the initial continuum ordinal. -/
lemma exists_set_enumeration (α : Type) [Countable α] [Infinite α] :
    ∃ f : CIndex → Set α, Function.Surjective f := by
  have hc : Cardinal.mk (Set α) = Cardinal.continuum := by
    rw [Cardinal.mk_set, Cardinal.mk_eq_aleph0]
    rfl
  obtain ⟨e⟩ := Cardinal.eq.mp (cindex_card.trans hc.symm)
  exact ⟨e, e.surjective⟩

lemma cardinal_prod_bool_lt {ι : Type} (hι : Cardinal.mk ι < Cardinal.continuum) :
    Cardinal.mk (ι × Bool) < Cardinal.continuum := by
  rw [Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_id]
  have hb : Cardinal.mk Bool ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite Bool).le
  calc
    _ ≤ max (Cardinal.mk ι) ℵ₀ * max (Cardinal.mk ι) ℵ₀ :=
      mul_le_mul' (le_max_left _ _) (hb.trans (le_max_right _ _))
    _ = max (Cardinal.mk ι) ℵ₀ := Cardinal.mul_eq_self (le_max_right _ _)
    _ < Cardinal.continuum := max_lt hι Cardinal.aleph0_lt_continuum
end InfiniteMatroidCounterexample
end

end OAI
