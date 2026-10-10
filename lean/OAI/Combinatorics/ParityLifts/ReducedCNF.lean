import OAI.Combinatorics.ParityLifts.ListPrograms

namespace OAI

namespace Sparsification

variable {α : Type} [DecidableEq α]

abbrev CNF (α : Type) := Finset (Finset α)

def Reduced (F : CNF α) : Prop :=
  ∀ C ∈ F, ∀ D ∈ F, C ⊆ D → C = D

def Holds (F : CNF α) (v : α → Prop) : Prop :=
  ∀ C ∈ F, ∃ x ∈ C, v x

def minimize (F : CNF α) : CNF α :=
  F.filter (fun C => ∀ D ∈ F, D ⊆ C → C ⊆ D)

lemma minimize_reduced (F : CNF α) : Reduced (minimize F) := by
  intro C hC D hD hCD
  exact Finset.Subset.antisymm hCD ((Finset.mem_filter.mp hD).2 C
    (Finset.mem_filter.mp hC).1 hCD)

lemma minimal_subclause (F : CNF α) (C : Finset α) (hC : C ∈ F) :
    ∃ D ∈ minimize F, D ⊆ C := by
  let S := F.filter (fun D => D ⊆ C)
  obtain ⟨D, hD, hm⟩ := Finset.exists_min_image S Finset.card ⟨C, by simp [S, hC]⟩
  refine ⟨D, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hD).1, ?_⟩,
    (Finset.mem_filter.mp hD).2⟩
  intro E hE hED
  have hES : E ∈ S := Finset.mem_filter.mpr ⟨hE, hED.trans (Finset.mem_filter.mp hD).2⟩
  have hc : D.card ≤ E.card := hm E hES
  have he := Finset.eq_of_subset_of_card_le hED hc
  exact he.symm.subset

lemma minimize_holds (F : CNF α) (v : α → Prop) : Holds (minimize F) v ↔ Holds F v := by
  constructor
  · intro h C hC
    obtain ⟨D, hD, hDC⟩ := minimal_subclause F C hC
    obtain ⟨x, hx, hv⟩ := h D hD
    exact ⟨x, hDC hx, hv⟩
  · intro h C hC
    exact h C (Finset.mem_filter.mp hC).1

/-- A new clause has no old subclause, including no equal old clause. -/
def Fresh (F A : CNF α) : Prop := ∀ D ∈ A, ∀ C ∈ F, ¬ C ⊆ D

def prune (F A : CNF α) : CNF α :=
  F.filter (fun C => ¬ ∃ D ∈ A, D ⊆ C) ∪ A

lemma prune_holds (F A : CNF α) (v : α → Prop) :
    Holds (prune F A) v ↔ Holds F v ∧ Holds A v := by
  classical
  constructor
  · intro h
    constructor
    · intro C hC
      by_cases he : ∃ D ∈ A, D ⊆ C
      · obtain ⟨D, hD, hDC⟩ := he
        obtain ⟨x, hx, hv⟩ := h D (Finset.mem_union_right _ hD)
        exact ⟨x, hDC hx, hv⟩
      · exact h C (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hC, he⟩))
    · intro C hC
      exact h C (Finset.mem_union_right _ hC)
  · rintro ⟨hF, hA⟩ C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact hF C (Finset.mem_filter.mp hC).1
    · exact hA C hC

lemma prune_reduced {F A : CNF α} (hF : Reduced F) (hA : Reduced A)
    (hf : Fresh F A) : Reduced (prune F A) := by
  intro C hC D hD hCD
  rcases Finset.mem_union.mp hC with hC | hC <;>
    rcases Finset.mem_union.mp hD with hD | hD
  · exact hF C (Finset.mem_filter.mp hC).1 D (Finset.mem_filter.mp hD).1 hCD
  · exact False.elim (hf D hD C (Finset.mem_filter.mp hC).1 hCD)
  · exact False.elim ((Finset.mem_filter.mp hD).2 ⟨C, hC, hCD⟩)
  · exact hA C hC D hD hCD

structure Flower (F : CNF α) (p q h : ℕ) where
  core : Finset α
  petals : CNF α
  core_card : core.card = p
  petals_card : petals.card = h
  petal_card : ∀ P ∈ petals, P.card = q
  apart : ∀ P ∈ petals, Disjoint core P
  pairwise : (↑petals : Set (Finset α)).Pairwise Disjoint
  cover : ∀ P ∈ petals, core ∪ P ∈ F

lemma Flower.core_fresh {F : CNF α} {p q h : ℕ} (f : Flower F p q h)
    (hF : Reduced F) (hq : 0 < q) (hh : 0 < h) : Fresh F {f.core} := by
  intro D hD C hC hCD
  have hD' : D = f.core := Finset.mem_singleton.mp hD
  subst D
  obtain ⟨P, hP⟩ := Finset.card_pos.mp (by rw [f.petals_card]; exact hh : 0 < f.petals.card)
  have hc := hF C hC (f.core ∪ P) (f.cover P hP) (hCD.trans Finset.subset_union_left)
  have hp : P ⊆ f.core := by rw [hc] at hCD; exact Finset.subset_union_right.trans hCD
  have he : P = ∅ := disjoint_self.mp ((f.apart P hP).mono_left hp)
  have := f.petal_card P hP
  simp [he] at this
  omega

lemma Flower.petals_fresh {F : CNF α} {p q h : ℕ} (f : Flower F p q h)
    (hF : Reduced F) (hp : 0 < p) : Fresh F f.petals := by
  intro P hP C hC hCP
  have hc := hF C hC (f.core ∪ P) (f.cover P hP) (hCP.trans Finset.subset_union_right)
  have hs : f.core ⊆ P := by rw [hc] at hCP; exact Finset.subset_union_left.trans hCP
  have he : f.core = ∅ := disjoint_self.mp ((f.apart P hP).mono_right hs)
  have := f.core_card
  simp [he] at this
  omega

lemma Flower.petals_reduced {F : CNF α} {p q h : ℕ} (f : Flower F p q h) :
    Reduced f.petals := by
  intro C hC D hD hCD
  apply Finset.eq_of_subset_of_card_le hCD
  rw [f.petal_card C hC, f.petal_card D hD]

lemma Flower.branch_holds {F : CNF α} {p q h : ℕ} (f : Flower F p q h)
    (v : α → Prop) :
    Holds F v ↔ Holds (prune F {f.core}) v ∨ Holds (prune F f.petals) v := by
  classical
  simp only [prune_holds]
  constructor
  · intro hF
    by_cases hc : ∃ x ∈ f.core, v x
    · exact Or.inl ⟨hF, by intro C hC; obtain rfl := Finset.mem_singleton.mp hC; exact hc⟩
    · right
      refine ⟨hF, ?_⟩
      intro P hP
      obtain ⟨x, hx, hv⟩ := hF _ (f.cover P hP)
      rcases Finset.mem_union.mp hx with hx | hx
      · exact False.elim (hc ⟨x, hx, hv⟩)
      · exact ⟨x, hx, hv⟩
  · rintro (⟨hF, _⟩ | ⟨hF, _⟩) <;> exact hF

end Sparsification


namespace Sparsification

variable {α : Type} [DecidableEq α] [Fintype α]

def units (F : CNF α) : Finset α := Finset.univ.filter (fun x => ({x} : Finset α) ∈ F)

def binaries (F : CNF α) : CNF α := F.filter (fun C => C.card = 2)

def degree (M : CNF α) (x : α) : ℕ := (M.filter (fun C => x ∈ C)).card

@[simp] lemma mem_units (F : CNF α) (x : α) : x ∈ units F ↔ ({x} : Finset α) ∈ F := by
  simp [units]

omit [DecidableEq α] [Fintype α] in
lemma clause_eq_singleton {C : Finset α} {x : α} (hc : C.Nonempty) (hs : C ⊆ {x}) :
    C = {x} := by
  obtain ⟨y, hy⟩ := hc
  have he : y = x := Finset.mem_singleton.mp (hs hy)
  exact Finset.Subset.antisymm hs (by simpa [← he] using Finset.singleton_subset_iff.mpr hy)

lemma units_prune (F A : CNF α) (hA : ∀ C ∈ A, C.Nonempty) :
    units (prune F A) = units F ∪ units A := by
  ext x
  simp only [mem_units, Finset.mem_union]
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Or.inl (Finset.mem_filter.mp hx).1
    · exact Or.inr hx
  · rintro (hx | hx)
    · by_cases he : ∃ C ∈ A, C ⊆ {x}
      · obtain ⟨C, hC, hs⟩ := he
        have hc := clause_eq_singleton (hA C hC) hs
        exact Finset.mem_union_right _ (hc ▸ hC)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, he⟩)
    · exact Finset.mem_union_right _ hx

lemma units_disjoint_of_fresh {F A : CNF α} (hf : Fresh F A) :
    Disjoint (units F) (units A) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact hf {x} (mem_units A x |>.mp hy) {x} (mem_units F x |>.mp hx) (Finset.Subset.refl _)

lemma units_card_of_singletons (A : CNF α) (hA : ∀ C ∈ A, C.card = 1) :
    (units A).card = A.card := by
  have he : (units A).image (fun x => ({x} : Finset α)) = A := by
    ext C
    constructor
    · intro hmem
      obtain ⟨x, hx, hxc⟩ := Finset.mem_image.mp hmem
      rw [← hxc]
      exact (mem_units A x).mp hx
    · intro hC
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (hA C hC)
      exact Finset.mem_image.mpr ⟨x, (mem_units A x).mpr hC, rfl⟩
  calc
    _ = ((units A).image (fun x => ({x} : Finset α))).card :=
      (Finset.card_image_of_injective _ (fun _ _ h => Finset.singleton_injective h)).symm
    _ = _ := congrArg Finset.card he

lemma units_empty_of_binaries (A : CNF α) (hA : ∀ C ∈ A, C.card = 2) :
    units A = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have := hA {x} ((mem_units A x).mp hx)
  simp at this

lemma card_le_sum_degrees (M : CNF α) (hne : ∀ C ∈ M, C.Nonempty) :
    M.card ≤ ∑ x : α, degree M x := by
  have hs : M ⊆ Finset.univ.biUnion (fun x : α => M.filter (fun C => x ∈ C)) := by
    intro C hC
    obtain ⟨x, hx⟩ := hne C hC
    exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hC, hx⟩⟩
  exact (Finset.card_le_card hs).trans Finset.card_biUnion_le

lemma marked_card_bound (M : CNF α) (h : ℕ) (hne : ∀ C ∈ M, C.Nonempty)
    (hd : ∀ x, degree M x ≤ h) : M.card ≤ Fintype.card α * h := by
  calc
    _ ≤ ∑ x : α, degree M x := card_le_sum_degrees M hne
    _ ≤ ∑ _x : α, h := Finset.sum_le_sum (fun x _ => hd x)
    _ = _ := by simp

def survived (M A : CNF α) : CNF α := M.filter (fun C => ¬ ∃ D ∈ A, D ⊆ C)

omit [Fintype α] in
lemma degree_survived_le (M A : CNF α) (x : α) : degree (survived M A) x ≤ degree M x := by
  apply Finset.card_le_card
  intro C hC
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).1,
    (Finset.mem_filter.mp hC).2⟩

lemma removed_card_bound (M A : CNF α) (h : ℕ)
    (hA : ∀ C ∈ A, C.card = 1) (hd : ∀ x, degree M x ≤ h) :
    M.card ≤ (survived M A).card + h * A.card := by
  have hs : M ⊆ survived M A ∪ (units A).biUnion (fun x => M.filter (fun C => x ∈ C)) := by
    intro C hC
    by_cases he : ∃ D ∈ A, D ⊆ C
    · obtain ⟨D, hD, hDC⟩ := he
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (hA D hD)
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨x, (mem_units A x).mpr hD, Finset.mem_filter.mpr
          ⟨hC, Finset.singleton_subset_iff.mp hDC⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hC, he⟩)
  calc
    _ ≤ (survived M A ∪ (units A).biUnion (fun x => M.filter (fun C => x ∈ C))).card :=
      Finset.card_le_card hs
    _ ≤ (survived M A).card + ((units A).biUnion (fun x => M.filter (fun C => x ∈ C))).card :=
      Finset.card_union_le _ _
    _ ≤ (survived M A).card + ∑ x ∈ units A, degree M x :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ (survived M A).card + ∑ _x ∈ units A, h :=
      Nat.add_le_add_left (Finset.sum_le_sum (fun x _ => hd x)) _
    _ = _ := by simp [units_card_of_singletons A hA, Nat.mul_comm]

lemma units_prune_card (F A : CNF α) (hf : Fresh F A) (hA : ∀ C ∈ A, C.card = 1) :
    (units (prune F A)).card = (units F).card + A.card := by
  rw [units_prune F A (fun C hC => Finset.card_pos.mp (by rw [hA C hC]; omega)),
    Finset.card_union_of_disjoint (units_disjoint_of_fresh hf), units_card_of_singletons A hA]

lemma unit_resource {F M A : CNF α} {a h : ℕ} (hf : Fresh F A)
    (hA : ∀ C ∈ A, C.card = 1) (hd : ∀ x, degree M x ≤ h)
    (hi : a ≤ M.card + h * (units F).card) :
    a ≤ (survived M A).card + h * (units (prune F A)).card := by
  have hr := removed_card_bound M A h hA hd
  rw [units_prune_card F A hf hA, Nat.mul_add]
  omega

omit [Fintype α] in
lemma survived_binary_eq {F M A : CNF α} (hf : Fresh F A) (hM : M ⊆ binaries F)
    (hA : ∀ C ∈ A, C.card = 2) : survived M A = M := by
  apply Finset.filter_eq_self.mpr
  intro C hC
  rintro ⟨D, hD, hDC⟩
  have hm := Finset.mem_filter.mp (hM hC)
  have he : D = C := Finset.eq_of_subset_of_card_le hDC (by rw [hA D hD, hm.2])
  exact hf D hD C hm.1 (he ▸ (Finset.Subset.refl _))

omit [DecidableEq α] [Fintype α] in
lemma marked_binary_disjoint {F M A : CNF α} (hf : Fresh F A) (hM : M ⊆ binaries F) :
    Disjoint M A := by
  apply Finset.disjoint_left.mpr
  intro C hC hA
  exact hf C hA C (Finset.mem_filter.mp (hM hC)).1 (Finset.Subset.refl _)

lemma binary_resource {F M A : CNF α} {a h : ℕ} (hf : Fresh F A)
    (hM : M ⊆ binaries F) (hA : ∀ C ∈ A, C.card = 2)
    (hi : a ≤ M.card + h * (units F).card) :
    a + A.card ≤ (M ∪ A).card + h * (units (prune F A)).card := by
  rw [Finset.card_union_of_disjoint (marked_binary_disjoint hf hM),
    units_prune F A (fun C hC => Finset.card_pos.mp (by rw [hA C hC]; omega)),
    units_empty_of_binaries A hA, Finset.union_empty]
  omega

omit [Fintype α] in
lemma degree_union_le (M A : CNF α) (x : α) :
    degree (M ∪ A) x ≤ degree M x + degree A x := by
  unfold degree
  rw [Finset.filter_union]
  exact Finset.card_union_le _ _

omit [Fintype α] in
lemma degree_le_of_subset (M F : CNF α) (hM : M ⊆ F) (x : α) : degree M x ≤ degree F x := by
  apply Finset.card_le_card
  intro C hC
  exact Finset.mem_filter.mpr
    ⟨hM (Finset.mem_filter.mp hC).1, (Finset.mem_filter.mp hC).2⟩

omit [Fintype α] in
lemma binary_degree_invariant {F M A : CNF α} {h : ℕ} (hM : M ⊆ binaries F)
    (hF : ∀ x, degree (binaries F) x < h) (hA : ∀ x, degree A x ≤ 1) :
    ∀ x, degree (M ∪ A) x ≤ h := by
  intro x
  have h1 := degree_union_le M A x
  have h2 := degree_le_of_subset M (binaries F) hM x
  have h3 := hF x
  have h4 := hA x
  omega

end Sparsification

end OAI
