import Mathlib

namespace OAI

namespace Invariant233.AtomOrbit

open scoped BigOperators

variable {α : Type*} [DistribLattice α] [BoundedOrder α]
variable (mass : α → ℝ)
variable (mass_bot : mass ⊥ = 0)
variable (mass_mono : Monotone mass)
variable (mass_sup : ∀ a b, Disjoint a b → mass (a ⊔ b) = mass a + mass b)

include mass_bot mass_sup in

theorem mass_finset_sup_of_atoms (s : Finset α)
    (hs : ∀ a ∈ s, IsAtom a) :
    mass (s.sup id) = ∑ a ∈ s, mass a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mass_bot
  | @insert a s ha ih =>
    have hsa : IsAtom a := hs a (Finset.mem_insert_self a s)
    have hss : ∀ b ∈ s, IsAtom b := fun b hb => hs b (Finset.mem_insert_of_mem hb)
    have hd : Disjoint a (s.sup id) := by
      apply Finset.disjoint_sup_right.mpr
      intro b hb
      exact hsa.disjoint_of_ne (hss b hb) (fun hab => ha (hab ▸ hb))
    rw [Finset.sup_insert]
    change mass (a ⊔ s.sup id) = ∑ b ∈ insert a s, mass b
    rw [mass_sup a (s.sup id) hd, ih hss, Finset.sum_insert ha]

include mass_bot mass_mono mass_sup in

theorem sum_atoms_le_total (s : Finset α) (hs : ∀ a ∈ s, IsAtom a) :
    (∑ a ∈ s, mass a) ≤ mass ⊤ := by
  rw [← mass_finset_sup_of_atoms mass mass_bot mass_sup s hs]
  exact mass_mono le_top

include mass_bot mass_mono mass_sup in

theorem finite_atoms_mass_ge {δ : ℝ} (hδ : 0 < δ) :
    {a : α | IsAtom a ∧ δ ≤ mass a}.Finite := by
  classical
  by_contra hfin
  have hinf : Set.Infinite {a : α | IsAtom a ∧ δ ≤ mass a} := hfin
  obtain ⟨n, hn⟩ := exists_nat_gt (mass ⊤ / δ)
  obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq n
  have hsmall : (n : ℝ) * δ ≤ ∑ a ∈ s, mass a := by
    calc
      (n : ℝ) * δ = ∑ _a ∈ s, δ := by simp [hcard]
      _ ≤ ∑ a ∈ s, mass a := Finset.sum_le_sum fun a ha => (hs ha).2
  have hbound := sum_atoms_le_total mass mass_bot mass_mono mass_sup s
    (fun a ha => (hs ha).1)
  have hlarge : mass ⊤ < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
  linarith

theorem isAtom_iterate (e : α ≃o α) {a : α} (ha : IsAtom a) (n : ℕ) :
    IsAtom ((e : α → α)^[n] a) := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (e.isAtom_iff _).mpr ih

omit [BoundedOrder α] in
theorem mass_iterate [BoundedOrder α] (e : α ≃o α) (he : ∀ a, mass (e a) = mass a)
    (a : α) (n : ℕ) : mass ((e : α → α)^[n] a) = mass a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', he, ih]

include mass_bot mass_mono mass_sup in

theorem finite_orbit_of_atom (e : α ≃o α) (he : ∀ a, mass (e a) = mass a)
    {a : α} (ha : IsAtom a) (hpos : 0 < mass a) :
    (Set.range fun n : ℕ => (e : α → α)^[n] a).Finite := by
  apply (finite_atoms_mass_ge mass mass_bot mass_mono mass_sup hpos).subset
  rintro b ⟨n, rfl⟩
  exact ⟨isAtom_iterate e ha n, (mass_iterate mass e he a n).ge⟩

omit [BoundedOrder α] in
theorem exists_pos_period_of_finite_orbit [BoundedOrder α] (e : α ≃o α) (a : α)
    (hfin : (Set.range fun n : ℕ => (e : α → α)^[n] a).Finite) :
    ∃ n : ℕ, 0 < n ∧ (e : α → α)^[n] a = a := by
  classical
  have hnot : ¬ Function.Injective (fun n : ℕ => (e : α → α)^[n] a) := by
    intro hinj
    exact (Set.infinite_range_of_injective hinj) hfin
  simp only [Function.Injective, not_forall] at hnot
  obtain ⟨m, n, heq, hne⟩ := hnot
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨n - m, Nat.sub_pos_of_lt hlt, Function.iterate_cancel e.injective heq.symm⟩
  · exact ⟨m - n, Nat.sub_pos_of_lt hlt, Function.iterate_cancel e.injective heq⟩

include mass_bot mass_mono mass_sup in

theorem exists_pos_period_of_atom (e : α ≃o α) (he : ∀ a, mass (e a) = mass a)
    {a : α} (ha : IsAtom a) (hpos : 0 < mass a) :
    ∃ n : ℕ, 0 < n ∧ (e : α → α)^[n] a = a :=
  exists_pos_period_of_finite_orbit e a
    (finite_orbit_of_atom mass mass_bot mass_mono mass_sup e he ha hpos)

include mass_bot mass_mono mass_sup in

theorem atom_eq_top_of_total_ergodicity (e : α ≃o α)
    (he : ∀ a, mass (e a) = mass a)
    (hfaithful : ∀ a, a ≠ ⊥ → 0 < mass a)
    (htotal : ∀ (n : ℕ), 0 < n → ∀ a, (e : α → α)^[n] a = a → a = ⊥ ∨ a = ⊤)
    {a : α} (ha : IsAtom a) : a = ⊤ := by
  obtain ⟨n, hn, hperiod⟩ := exists_pos_period_of_atom mass mass_bot mass_mono
    mass_sup e he ha (hfaithful a ha.ne_bot)
  exact (htotal n hn a hperiod).resolve_left ha.ne_bot

include mass_bot mass_mono mass_sup in

theorem no_atoms_of_total_ergodicity (e : α ≃o α)
    (he : ∀ a, mass (e a) = mass a)
    (hfaithful : ∀ a, a ≠ ⊥ → 0 < mass a)
    (htotal : ∀ (n : ℕ), 0 < n → ∀ a, (e : α → α)^[n] a = a → a = ⊥ ∨ a = ⊤)
    (hnontrivial : ∃ b : α, b ≠ ⊥ ∧ b ≠ ⊤) :
    ∀ a : α, ¬ IsAtom a := by
  intro a ha
  have hatop := atom_eq_top_of_total_ergodicity mass mass_bot mass_mono mass_sup
    e he hfaithful htotal ha
  obtain ⟨b, hb0, hb1⟩ := hnontrivial
  have hbat : b ≤ a := hatop ▸ le_top
  exact (ha.le_iff.mp hbat).elim hb0 (fun hba => hb1 (hba.trans hatop))

end Invariant233.AtomOrbit

end OAI
