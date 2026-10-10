import Mathlib

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

variable {V : Type*} [DecidableEq V]
abbrev F₂ := ZMod 2
abbrev Chain (K : PreAbstractSimplicialComplex V) := {s : Finset V // s ∈ K} →₀ F₂

noncomputable def simplex (K : PreAbstractSimplicialComplex V) (s : Finset V) : Chain K := by
  classical
  exact if h : s ∈ K then Finsupp.single ⟨s, h⟩ 1 else 0

omit [DecidableEq V] in
lemma simplex_of_mem (K : PreAbstractSimplicialComplex V) {s : Finset V} (hs : s ∈ K) :
    simplex K s = Finsupp.single ⟨s, hs⟩ 1 := by simp [simplex, hs]

omit [DecidableEq V] in
@[simp] lemma simplex_empty (K : PreAbstractSimplicialComplex V) : simplex K ∅ = 0 := by
  have h : (∅ : Finset V) ∉ K := fun h => (K.isRelLowerSet_faces h).1.ne_empty rfl
  simp [simplex, h]

noncomputable def boundary (K : PreAbstractSimplicialComplex V) : Chain K →ₗ[F₂] Chain K := by
  classical
  exact Finsupp.linearCombination F₂ (fun s => ∑ a ∈ s.val, simplex K (s.val.erase a))

lemma boundary_simplex (K : PreAbstractSimplicialComplex V) {s : Finset V} (hs : s ∈ K) :
    boundary K (simplex K s) = ∑ a ∈ s, simplex K (s.erase a) := by
  classical
  simp [simplex_of_mem K hs, boundary, Finsupp.linearCombination_single]

lemma boundary_simplex_subset (K : PreAbstractSimplicialComplex V)
    {s t : Finset V} (ht : t ∈ K) (hs : s ⊆ t) :
    boundary K (simplex K s) = ∑ a ∈ s, simplex K (s.erase a) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact boundary_simplex K ((K.isRelLowerSet_faces ht).2 hs hn)

omit [DecidableEq V] in
lemma chain_add_self (K : PreAbstractSimplicialComplex V) (c : Chain K) : c + c = 0 := by
  ext s
  exact CharTwo.add_self_eq_zero _

lemma double_erase_sum (K : PreAbstractSimplicialComplex V) (s : Finset V) :
    (∑ a ∈ s, ∑ b ∈ s.erase a, simplex K ((s.erase a).erase b)) = 0 := by
  classical
  let g (p : V × V) : Chain K := if p.1 = p.2 then 0 else simplex K ((s.erase p.1).erase p.2)
  have hg : (∑ a ∈ s, ∑ b ∈ s.erase a, simplex K ((s.erase a).erase b)) =
      ∑ p ∈ s ×ˢ s, g p := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [← Finset.filter_ne, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _hb
    by_cases hab : a = b <;> simp [g, hab, Finset.filter_ne]
  rw [hg]
  apply Finset.sum_involution (fun p _ => p.swap)
  · intro p hp
    dsimp [g]
    by_cases he : p.1 = p.2
    · simp [he]
    · simp only [he, ite_false, Ne.symm he, Finset.erase_right_comm]
      exact chain_add_self K _
  · intro p hp hg he
    have h : p.1 = p.2 := congrArg Prod.snd he
    exact hg (by simp [g, h])
  · intro p hp
    exact Prod.swap_swap p
  · intro p hp
    exact Finset.mem_product.mpr (And.symm (Finset.mem_product.mp hp))

lemma boundary_twice_simplex (K : PreAbstractSimplicialComplex V)
    {s : Finset V} (hs : s ∈ K) : boundary K (boundary K (simplex K s)) = 0 := by
  classical
  rw [boundary_simplex K hs, map_sum]
  have h (a : V) : boundary K (simplex K (s.erase a)) =
      ∑ b ∈ s.erase a, simplex K ((s.erase a).erase b) :=
    boundary_simplex_subset K hs (Finset.erase_subset a s)
  simp_rw [h]
  exact double_erase_sum K s

lemma boundary_sq (K : PreAbstractSimplicialComplex V) :
    (boundary K).comp (boundary K) = 0 := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := boundary_twice_simplex K s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs, smul_zero, LinearMap.zero_apply]

noncomputable def augmentation (K : PreAbstractSimplicialComplex V) : Chain K →ₗ[F₂] F₂ :=
  Finsupp.linearCombination F₂ (fun s => if s.val.card = 1 then 1 else 0)

omit [DecidableEq V] in
lemma augmentation_simplex (K : PreAbstractSimplicialComplex V) {s : Finset V} (hs : s ∈ K) :
    augmentation K (simplex K s) = if s.card = 1 then 1 else 0 := by
  simp [simplex_of_mem K hs, augmentation, Finsupp.linearCombination_single]

omit [DecidableEq V] in
lemma augmentation_simplex_subset (K : PreAbstractSimplicialComplex V)
    {s t : Finset V} (ht : t ∈ K) (hs : s ⊆ t) :
    augmentation K (simplex K s) = if s.card = 1 then 1 else 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact augmentation_simplex K ((K.isRelLowerSet_faces ht).2 hs hn)

lemma augmentation_boundary_simplex (K : PreAbstractSimplicialComplex V)
    {s : Finset V} (hs : s ∈ K) : augmentation K (boundary K (simplex K s)) = 0 := by
  classical
  rw [boundary_simplex K hs, map_sum]
  have hh (a : V) (ha : a ∈ s) : augmentation K (simplex K (s.erase a)) =
      if s.card = 2 then 1 else 0 := by
    rw [augmentation_simplex_subset K hs (Finset.erase_subset a s), Finset.card_erase_of_mem ha]
    have hc : s.card - 1 = 1 ↔ s.card = 2 := by omega
    simp only [hc]
  rw [Finset.sum_congr rfl hh]
  by_cases hc : s.card = 2
  · simpa [hc] using (show (2 : F₂) = 0 by decide)
  · simp [hc]

lemma augmentation_boundary (K : PreAbstractSimplicialComplex V) :
    (augmentation K).comp (boundary K) = 0 := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := augmentation_boundary_simplex K s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs, smul_zero, LinearMap.zero_apply]

end BorsukNine.SimplicialChains

end OAI
