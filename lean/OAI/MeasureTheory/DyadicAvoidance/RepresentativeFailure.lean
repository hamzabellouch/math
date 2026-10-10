import Mathlib

namespace OAI

universe u_Ω u_T u_I u_J

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Problem310.RepresentativeFailure

/-- A deterministic finite representative list turns a pointwise failure bound
into an all-parameters bound. No measurability of the existential event is
needed: the outer-measure union bound is sufficient. -/
theorem failure_le_card_mul {Ω : Type u_Ω} {T : Type u_T} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (K : Set T) (R : Finset T)
    (failure test : Ω → T → Prop) (q : ℝ≥0∞)
    (htransfer : ∀ ω ∈ A, ∀ t ∈ K, failure ω t → ∃ r ∈ R, test ω r)
    (hbound : ∀ r ∈ R, μ {ω | ω ∈ A ∧ test ω r} ≤ q) :
    μ {ω | ω ∈ A ∧ ∃ t ∈ K, failure ω t} ≤ R.card * q := by
  classical
  have hsub : {ω | ω ∈ A ∧ ∃ t ∈ K, failure ω t} ⊆
      ⋃ r ∈ R, {ω | ω ∈ A ∧ test ω r} := by
    rintro ω ⟨hω, t, ht, hf⟩
    obtain ⟨r, hr, htest⟩ := htransfer ω hω t ht hf
    exact mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hr, hω, htest⟩⟩
  calc
    μ {ω | ω ∈ A ∧ ∃ t ∈ K, failure ω t}
        ≤ μ (⋃ r ∈ R, {ω | ω ∈ A ∧ test ω r}) := measure_mono hsub
    _ ≤ ∑ r ∈ R, μ {ω | ω ∈ A ∧ test ω r} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _r ∈ R, q := Finset.sum_le_sum hbound
    _ = R.card * q := by simp [nsmul_eq_mul]

/-- Predicate agreement for the finite representative list supplies the
transfer hypothesis in the local-routing argument. -/
theorem local_failure_le_card_mul {Ω : Type u_Ω} {T : Type u_T} {I : Type u_I} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (K : Set T) (R : Finset T)
    (failure : Ω → T → Prop) (localHit : Ω → I → T → Prop) (q : ℝ≥0∞)
    (hlocal : ∀ ω ∈ A, ∀ t ∈ K, failure ω t → ∀ i, ¬ localHit ω i t)
    (hreps : ∀ t ∈ K, ∃ r ∈ R,
      ∀ ω ∈ A, ∀ i, localHit ω i r ↔ localHit ω i t)
    (hbound : ∀ r ∈ R, μ {ω | ω ∈ A ∧ ∀ i, ¬ localHit ω i r} ≤ q) :
    μ {ω | ω ∈ A ∧ ∃ t ∈ K, failure ω t} ≤ R.card * q := by
  apply failure_le_card_mul μ A K R failure (fun ω t => ∀ i, ¬ localHit ω i t) q ?_ hbound
  intro ω hω t ht hf
  obtain ⟨r, hr, hagree⟩ := hreps t ht
  refine ⟨r, hr, ?_⟩
  intro i hi
  exact hlocal ω hω t ht hf i ((hagree ω hω i).mp hi)

/-- The multiplicative form used for an exposure atom: a per-representative
joint bound `q * μ A` and an entropy budget `card R * q ≤ p` give the
all-scales joint bound `p * μ A`. -/
theorem local_failure_le_mul_mass {Ω : Type u_Ω} {T : Type u_T} {I : Type u_I} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (K : Set T) (R : Finset T)
    (failure : Ω → T → Prop) (localHit : Ω → I → T → Prop) (p q : ℝ≥0∞)
    (hlocal : ∀ ω ∈ A, ∀ t ∈ K, failure ω t → ∀ i, ¬ localHit ω i t)
    (hreps : ∀ t ∈ K, ∃ r ∈ R,
      ∀ ω ∈ A, ∀ i, localHit ω i r ↔ localHit ω i t)
    (hbound : ∀ r ∈ R, μ {ω | ω ∈ A ∧ ∀ i, ¬ localHit ω i r} ≤ q * μ A)
    (hbudget : R.card * q ≤ p) :
    μ {ω | ω ∈ A ∧ ∃ t ∈ K, failure ω t} ≤ p * μ A := by
  calc
    μ {ω | ω ∈ A ∧ ∃ t ∈ K, failure ω t} ≤ R.card * (q * μ A) :=
      local_failure_le_card_mul μ A K R failure localHit (q * μ A) hlocal hreps hbound
    _ = (R.card * q) * μ A := (mul_assoc _ _ _).symm
    _ ≤ p * μ A := mul_le_mul hbudget le_rfl (by positivity) (by positivity)

/-- Sum restricted failure estimates over exposure atoms and pay once for the
exceptional event on which the first default does not exist. The mass bound
is separated out so this works for finite partitions, subpartitions, and
any finite-family construction with total mass at most one. -/
theorem failure_le_bad_add_atom_bound {Ω : Type u_Ω} {J : Type u_J} [MeasurableSpace Ω] [Fintype J]
    (μ : Measure Ω) (F D : Set Ω) (A : J → Set Ω) (p q : ℝ≥0∞)
    (hcover : F ⊆ D ∪ ⋃ j, A j)
    (hbad : μ D ≤ q)
    (hatom : ∀ j, μ (F ∩ A j) ≤ p * μ (A j))
    (hmass : ∑ j, μ (A j) ≤ 1) : μ F ≤ q + p := by
  classical
  have hsub : F ⊆ D ∪ ⋃ j, F ∩ A j := by
    intro ω hω
    rcases hcover hω with hD | hA
    · exact Or.inl hD
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hA
      exact Or.inr (mem_iUnion.mpr ⟨j, hω, hj⟩)
  calc
    μ F ≤ μ (D ∪ ⋃ j, F ∩ A j) := measure_mono hsub
    _ ≤ μ D + μ (⋃ j, F ∩ A j) := measure_union_le _ _
    _ ≤ q + ∑ j, μ (F ∩ A j) :=
      add_le_add hbad (measure_iUnion_fintype_le μ (fun j => F ∩ A j))
    _ ≤ q + ∑ j, p * μ (A j) := add_le_add le_rfl (Finset.sum_le_sum fun j _ => hatom j)
    _ = q + p * ∑ j, μ (A j) := by rw [Finset.mul_sum]
    _ ≤ q + p * 1 := add_le_add le_rfl (mul_le_mul le_rfl hmass (by positivity) (by positivity))
    _ = q + p := by rw [mul_one]

/-- The all-scales probability estimate, abstracted from the
finite table construction. Good exposure atoms may have different trial
types, representatives and fixed-scale failure probabilities. -/
theorem raw_failure_le_two_budgets {Ω : Type u_Ω} {T : Type u_T} {J : Type u_J} [MeasurableSpace Ω] [Fintype J]
    (μ : Measure Ω) (K : Set T) (D : Set Ω) (A : J → Set Ω)
    (I : J → Type u_I) (R : J → Finset T) (failure : Ω → T → Prop)
    (localHit : ∀ j, Ω → I j → T → Prop) (p q : ℝ≥0∞) (rate : J → ℝ≥0∞)
    (hcover : univ ⊆ D ∪ ⋃ j, A j) (hbad : μ D ≤ q)
    (hmass : ∑ j, μ (A j) ≤ 1)
    (hlocal : ∀ j, ∀ ω ∈ A j, ∀ t ∈ K, failure ω t → ∀ i, ¬ localHit j ω i t)
    (hreps : ∀ j, ∀ t ∈ K, ∃ r ∈ R j,
      ∀ ω ∈ A j, ∀ i, localHit j ω i r ↔ localHit j ω i t)
    (hbound : ∀ j, ∀ r ∈ R j,
      μ {ω | ω ∈ A j ∧ ∀ i, ¬ localHit j ω i r} ≤ rate j * μ (A j))
    (hbudget : ∀ j, (R j).card * rate j ≤ p) :
    μ {ω | ∃ t ∈ K, failure ω t} ≤ q + p := by
  apply failure_le_bad_add_atom_bound μ {ω | ∃ t ∈ K, failure ω t} D A p q
    ((subset_univ _).trans hcover) hbad ?_ hmass
  intro j
  have h := local_failure_le_mul_mass μ (A j) K (R j) failure (localHit j) p (rate j)
    (hlocal j) (hreps j) (hbound j) (hbudget j)
  simpa only [Set.ofPred_and, Set.ofPred_mem_eq, Set.inter_comm] using h

end Problem310.RepresentativeFailure

end

end OAI
