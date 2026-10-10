import OAI.Combinatorics.Ryser.Construction.CosetDirections
import OAI.Combinatorics.Ryser.Construction.ExtraDirections

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [Fintype k]

def embeddedDirections (σ : k →+* F) : Finset (Direction F) :=
  Finset.univ.image (mapDirection σ)

def groupPlacement (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    ConfigurationGroup σ → PlaneLinearMap F
  | none => PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)
  | some c => cosetPlacement σ c

def groupAltered (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : Finset (Direction F) :=
  alteredDirections σ (groupPlacement σ u v huv i)

def groupAxes (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : Finset (Direction F) :=
  axisDirections σ (groupPlacement σ u v huv i)

def groupConflict (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : Finset (Direction F) := by
  classical
  exact match i with
  | none => embeddedDirections σ
  | some c => if c = 1 then embeddedDirections σ else groupAltered σ u v huv (some c)

theorem groupAltered_card (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) :
    (groupAltered σ u v huv i).card = Fintype.card k - 1 :=
  card_alteredDirections σ _

theorem groupAxes_card (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : (groupAxes σ u v huv i).card = 2 :=
  card_axisDirections σ _

theorem embeddedDirections_card (σ : k →+* F) :
    (embeddedDirections σ).card = Fintype.card k + 1 := by
  rw [embeddedDirections, Finset.card_image_of_injective _ (mapDirection_injective σ),
    Finset.card_univ, Fintype.card_option]

theorem coset_altered_embedded_index (σ : k →+* F) {c : CosetIndex σ}
    {d : Direction F} (hc : d ∈ alteredDirections σ (cosetPlacement σ c))
    (hd : d ∈ embeddedDirections σ) : c = 1 := by
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp hd
  cases e with
  | none =>
      have he' : d = none := he.symm
      subst d
      exact (none_notMem_coset_altered σ c hc).elim
  | some t =>
      have he' : d = some (σ t) := he.symm
      subst d
      have ht : t ≠ 0 := by
        intro ht
        subst t
        exact zero_notMem_coset_altered σ c (by simp [mapDirection] at hc)
      have h1 : some (σ t) ∈ alteredDirections σ (cosetPlacement σ 1) := by
        apply (mem_coset_altered_iff σ 1 _).mpr
        exact ⟨t, ht, by simp⟩
      exact coset_altered_index_eq σ hc h1

theorem identity_altered_subset_embedded (σ : k →+* F) :
    alteredDirections σ (cosetPlacement σ 1) ⊆ embeddedDirections σ := by
  intro d hd
  obtain ⟨t, ht, rfl⟩ := (mem_coset_altered_iff σ 1 d).mp hd
  apply Finset.mem_image.mpr
  exact ⟨some t, Finset.mem_univ _, by simp [mapDirection]⟩

theorem groupAltered_subset_conflict (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : groupAltered σ u v huv i ⊆ groupConflict σ u v huv i := by
  classical
  cases i with
  | none =>
      intro d hd
      change d ∈ embeddedDirections σ
      change d ∈ alteredDirections σ
        (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) at hd
      rw [extra_alteredDirections σ u v huv] at hd
      exact (Finset.mem_sdiff.mp hd).1
  | some c =>
      by_cases hc : c = 1
      · subst c
        simpa [groupConflict, groupAltered, groupPlacement] using
          identity_altered_subset_embedded σ
      · simp only [groupConflict, ite_eq_right hc]
        exact Finset.Subset.refl _

theorem exists_groupAltered (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hu : u ≠ 0) (hv : v ≠ 0) (d : Direction F) :
    ∃ i : ConfigurationGroup σ, d ∈ groupAltered σ u v huv i := by
  cases d with
  | none => exact ⟨none, none_mem_extra_alteredDirections σ u v huv⟩
  | some a =>
      by_cases ha : a = 0
      · subst a
        exact ⟨none, zero_mem_extra_alteredDirections σ u v huv hu hv⟩
      · obtain ⟨c, hc, _⟩ := existsUnique_coset_altered σ a ha
        exact ⟨some c, hc⟩

theorem shared_groupConflict (σ : k →+* F) (u v : k) (huv : u ≠ v)
    {i j : ConfigurationGroup σ} {d : Direction F} (hij : i ≠ j)
    (hi : d ∈ groupConflict σ u v huv i)
    (hj : d ∈ groupConflict σ u v huv j) :
    (i = none ∧ j = some 1) ∨ (i = some 1 ∧ j = none) := by
  classical
  cases i with
  | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some c =>
          have hc : c = 1 := by
            by_contra hc
            have hj' : d ∈ alteredDirections σ (cosetPlacement σ c) := by
              simpa [groupConflict, hc, groupAltered, groupPlacement] using hj
            exact hc (coset_altered_embedded_index σ hj' hi)
          exact Or.inl ⟨rfl, congrArg some hc⟩
  | some c =>
      cases j with
      | none =>
          have hc : c = 1 := by
            by_contra hc
            have hi' : d ∈ alteredDirections σ (cosetPlacement σ c) := by
              simpa [groupConflict, hc, groupAltered, groupPlacement] using hi
            exact hc (coset_altered_embedded_index σ hi' hj)
          exact Or.inr ⟨congrArg some hc, rfl⟩
      | some e =>
          have hce : c ≠ e := fun h => hij (congrArg some h)
          by_cases hc : c = 1
          · subst c
            have he : e ≠ 1 := Ne.symm hce
            have hj' : d ∈ alteredDirections σ (cosetPlacement σ e) := by
              simpa [groupConflict, he, groupAltered, groupPlacement] using hj
            have hi' : d ∈ embeddedDirections σ := by simpa [groupConflict] using hi
            exact (he (coset_altered_embedded_index σ hj' hi')).elim
          · have hi' : d ∈ alteredDirections σ (cosetPlacement σ c) := by
              simpa [groupConflict, hc, groupAltered, groupPlacement] using hi
            by_cases he : e = 1
            · subst e
              have hj' : d ∈ embeddedDirections σ := by simpa [groupConflict] using hj
              exact (hc (coset_altered_embedded_index σ hi' hj')).elim
            · have hj' : d ∈ alteredDirections σ (cosetPlacement σ e) := by
                simpa [groupConflict, he, groupAltered, groupPlacement] using hj
              exact (hce (coset_altered_index_eq σ hi' hj')).elim

theorem shared_groupAltered (σ : k →+* F) (u v : k) (huv : u ≠ v)
    {i j : ConfigurationGroup σ} {d : Direction F} (hij : i ≠ j)
    (hi : d ∈ groupAltered σ u v huv i)
    (hj : d ∈ groupAltered σ u v huv j) :
    (i = none ∧ j = some 1) ∨ (i = some 1 ∧ j = none) :=
  shared_groupConflict σ u v huv hij
    (groupAltered_subset_conflict σ u v huv i hi)
    (groupAltered_subset_conflict σ u v huv j hj)

section FiniteAmbient

variable [Fintype F]

theorem groupConflict_multiplicity_le_two (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (d : Direction F) :
    (Finset.univ.filter (fun i => d ∈ groupConflict σ u v huv i)).card ≤ 2 := by
  classical
  let I := Finset.univ.filter (fun i => d ∈ groupConflict σ u v huv i)
  by_cases hsingle : ∀ i ∈ I, ∀ j ∈ I, i = j
  · have hcard : I.card ≤ 1 := Finset.card_le_one.mpr hsingle
    exact hcard.trans (by decide)
  · push Not at hsingle
    obtain ⟨i, hi, j, hj, hij⟩ := hsingle
    have hsub : I ⊆ ({none, some 1} : Finset (ConfigurationGroup σ)) := by
      intro a ha
      by_cases hai : a = i
      · subst a
        rcases shared_groupConflict σ u v huv hij (Finset.mem_filter.mp hi).2
          (Finset.mem_filter.mp hj).2 with h | h
        · simp [h.1]
        · simp [h.1]
      · rcases shared_groupConflict σ u v huv hai (Finset.mem_filter.mp ha).2
          (Finset.mem_filter.mp hi).2 with h | h
        · simp [h.1]
        · simp [h.1]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem groupAltered_multiplicity_le_two (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (d : Direction F) :
    (Finset.univ.filter (fun i => d ∈ groupAltered σ u v huv i)).card ≤ 2 := by
  apply (Finset.card_le_card ?_).trans (groupConflict_multiplicity_le_two σ u v huv d)
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    groupAltered_subset_conflict σ u v huv i (Finset.mem_filter.mp hi).2⟩

end FiniteAmbient

end RyserCoveringCounterexample.Construction

end

end OAI
