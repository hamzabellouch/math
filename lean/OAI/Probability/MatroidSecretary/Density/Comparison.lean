import OAI.Probability.MatroidProphet.Main

namespace OAI

namespace MatroidProphet

open Set
variable {α : Type*} [Fintype α]
attribute [local instance] Classical.propDecidable

namespace DensityComparison

noncomputable def unionExpansion (M : Matroid α) (_hE : M.E = univ)
    (κ : ℕ) (D P : Set α) : Set α :=
  ⋃₀ {Q | IsDensityMax M κ D P Q}

theorem unionExpansion_eq (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) :
    unionExpansion M hE κ D P = densityExpansion M hE κ D P := by
  apply Set.Subset.antisymm
  · intro x hx
    change x ∈ ⋃₀ {Q | IsDensityMax M κ D P Q} at hx
    obtain ⟨Q, hQ, hxQ⟩ := Set.mem_sUnion.mp hx
    exact (densityExpansion_spec M hE κ D P).2 Q hQ hxQ
  · intro x hx
    change x ∈ ⋃₀ {Q | IsDensityMax M κ D P Q}
    exact Set.mem_sUnion.mpr
      ⟨densityExpansion M hE κ D P, (densityExpansion_spec M hE κ D P).1, hx⟩

noncomputable def guardedBirth (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) : ℤ :=
  if hex : ∃ j : ℕ, e ∈ nominalPath M hE κ D C h (activation h + j) then
    activation h + Nat.find hex
  else activation h

theorem guardedBirth_eq (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    guardedBirth M hE κ D C h e = nominalBirth M hE κ D C h e := by
  unfold guardedBirth
  rw [dite_eq_left (exists_nominal_member M hE κ D C h e)]
  rfl

end DensityComparison

lemma densityExpansion_eq_chosen (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) :
    densityExpansion M hE κ D P = (exists_largest_densityMax M hE κ D P).choose := by
  rfl

lemma nominalBirth_eq_find (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    nominalBirth M hE κ D C h e =
      activation h + Nat.find (exists_nominal_member M hE κ D C h e) := by
  rfl

end MatroidProphet

end OAI
