import OAI.Combinatorics.SecondNeighborhood.Matching
import Mathlib.Combinatorics.Hall.Finite

namespace OAI

namespace SeymourSecondNeighborhood.Bipartite

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable {E : L → R → Prop}

omit [DecidableEq L] [DecidableEq R] in
private theorem exists_minimum_vertexCover (E : L → R → Prop) :
    ∃ A : Finset L, ∃ B : Finset R, IsVertexCover E A B ∧
      ∀ A' B', IsVertexCover E A' B' → A.card + B.card ≤ A'.card + B'.card := by
  classical
  let covers : Finset (Finset L × Finset R) :=
    Finset.univ.filter (fun p => IsVertexCover E p.1 p.2)
  have hnonempty : covers.Nonempty := by
    refine ⟨(Finset.univ, ∅), ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun l _ _ => Or.inl (Finset.mem_univ l)⟩
  obtain ⟨p, hp, hleast⟩ :=
    covers.exists_min_image (fun p => p.1.card + p.2.card) hnonempty
  refine ⟨p.1, p.2, (Finset.mem_filter.mp hp).2, ?_⟩
  intro A' B' hC
  exact hleast (A', B') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩)

private theorem minimum_cover_left_hall {A : Finset L} {B : Finset R}
    (hC : IsVertexCover E A B)
    (hmin : ∀ A' B', IsVertexCover E A' B' →
      A.card + B.card ≤ A'.card + B'.card) :
    ∃ f : A → R, Function.Injective f ∧ ∀ a : A, E (a : L) (f a) ∧ f a ∉ B := by
  classical
  let t : A → Finset R := fun a => Finset.univ.filter (fun r => E a r ∧ r ∉ B)
  have hhall : ∀ s : Finset A, s.card ≤ (s.biUnion t).card := by
    intro s
    let S : Finset L := s.image (fun a : A => (a : L))
    let T : Finset R := s.biUnion t
    have hSA : S ⊆ A := by
      intro l hl
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hl
      exact a.property
    have hScard : S.card = s.card :=
      Finset.card_image_of_injective s Subtype.val_injective
    have hdisjoint : Disjoint B T := by
      apply Finset.disjoint_left.mpr
      intro r hrB hrT
      obtain ⟨a, _, hra⟩ := Finset.mem_biUnion.mp hrT
      exact (Finset.mem_filter.mp hra).2.2 hrB
    have hreplace : IsVertexCover E (A \ S) (B ∪ T) := by
      intro l r hlr
      by_cases hlS : l ∈ S
      · by_cases hrB : r ∈ B
        · exact Or.inr (Finset.mem_union_left _ hrB)
        · right
          apply Finset.mem_union_right
          obtain ⟨a, has, hal⟩ := Finset.mem_image.mp hlS
          apply Finset.mem_biUnion.mpr
          refine ⟨a, has, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hrB⟩⟩
          rw [hal]
          exact hlr
      · rcases hC l r hlr with hlA | hrB
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨hlA, hlS⟩)
        · exact Or.inr (Finset.mem_union_left _ hrB)
    have hbound := hmin (A \ S) (B ∪ T) hreplace
    rw [Finset.card_union_of_disjoint hdisjoint] at hbound
    have hsplit := Finset.card_sdiff_add_card_eq_card hSA
    rw [hScard] at hsplit
    change s.card ≤ T.card
    omega
  obtain ⟨f, hfinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  exact ⟨f, hfinj, fun a => (Finset.mem_filter.mp (hf a)).2⟩

private theorem minimum_cover_has_equal_matching {A : Finset L} {B : Finset R}
    (hC : IsVertexCover E A B)
    (hmin : ∀ A' B', IsVertexCover E A' B' →
      A.card + B.card ≤ A'.card + B'.card) :
    ∃ N : Finset (L × R), IsMatching E N ∧ N.card = A.card + B.card := by
  classical
  obtain ⟨f, hfinj, hf⟩ := minimum_cover_left_hall hC hmin
  have hCsym : IsVertexCover (fun r l => E l r) B A := by
    intro r l hlr
    exact (hC l r hlr).symm
  have hminsym : ∀ B' A', IsVertexCover (fun r l => E l r) B' A' →
      B.card + A.card ≤ B'.card + A'.card := by
    intro B' A' hC'
    have h := hmin A' B' (fun l r hlr => (hC' r l hlr).symm)
    omega
  obtain ⟨g, hginj, hg⟩ := minimum_cover_left_hall hCsym hminsym
  let P : Finset (L × R) := Finset.univ.image (fun a : A => ((a : L), f a))
  let Q : Finset (L × R) := Finset.univ.image (fun b : B => (g b, (b : R)))
  have hP : IsMatching E P := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
      exact (hf a).1
    · intro e he e' he' heq
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp he'
      have haa : a = a' := Subtype.ext heq
      subst a'
      rfl
    · intro e he e' he' heq
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp he'
      have haa : a = a' := hfinj heq
      subst a'
      rfl
  have hQ : IsMatching E Q := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he
      exact (hg b).1
    · intro e he e' he' heq
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨b', _, rfl⟩ := Finset.mem_image.mp he'
      have hbb : b = b' := hginj heq
      subst b'
      rfl
    · intro e he e' he' heq
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨b', _, rfl⟩ := Finset.mem_image.mp he'
      have hbb : b = b' := Subtype.ext heq
      subst b'
      rfl
  have hcrossL : ∀ e ∈ P, ∀ e' ∈ Q, e.1 ≠ e'.1 := by
    intro e he e' he' heq
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he'
    change (a : L) = g b at heq
    apply (hg b).2
    rw [← heq]
    exact a.property
  have hcrossR : ∀ e ∈ P, ∀ e' ∈ Q, e.2 ≠ e'.2 := by
    intro e he e' he' heq
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he'
    change f a = (b : R) at heq
    apply (hf a).2
    rw [heq]
    exact b.property
  have hmatch : IsMatching E (P ∪ Q) := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact hP.1 e he
      · exact hQ.1 e he
    · intro e he e' he' heq
      rcases Finset.mem_union.mp he with he | he <;>
        rcases Finset.mem_union.mp he' with he' | he'
      · exact hP.2.1 he he' heq
      · exact False.elim (hcrossL e he e' he' heq)
      · exact False.elim (hcrossL e' he' e he heq.symm)
      · exact hQ.2.1 he he' heq
    · intro e he e' he' heq
      rcases Finset.mem_union.mp he with he | he <;>
        rcases Finset.mem_union.mp he' with he' | he'
      · exact hP.2.2 he he' heq
      · exact False.elim (hcrossR e he e' he' heq)
      · exact False.elim (hcrossR e' he' e he heq.symm)
      · exact hQ.2.2 he he' heq
  have hdisjoint : Disjoint P Q :=
    Finset.disjoint_left.mpr (fun e he he' => hcrossL e he e he' rfl)
  have hPinj : Function.Injective (fun a : A => ((a : L), f a)) := by
    intro a a' h
    exact Subtype.ext (congrArg Prod.fst h)
  have hQinj : Function.Injective (fun b : B => (g b, (b : R))) := by
    intro b b' h
    exact Subtype.ext (congrArg Prod.snd h)
  have hPcard : P.card = A.card := by
    dsimp [P]
    rw [Finset.card_image_of_injective _ hPinj]
    simp
  have hQcard : Q.card = B.card := by
    dsimp [Q]
    rw [Finset.card_image_of_injective _ hQinj]
    simp
  exact ⟨P ∪ Q, hmatch, by rw [Finset.card_union_of_disjoint hdisjoint, hPcard, hQcard]⟩

theorem exists_vertexCover_card_eq_of_isMaximumMatching {M : Finset (L × R)}
    (hM : IsMaximumMatching E M) :
    ∃ A : Finset L, ∃ B : Finset R,
      IsVertexCover E A B ∧ A.card + B.card = M.card ∧
      (∀ l ∈ A, ∃ r, E l r) ∧ (∀ r ∈ B, ∃ l, E l r) := by
  classical
  obtain ⟨A, B, hC, hmin⟩ := exists_minimum_vertexCover E
  obtain ⟨N, hN, hNcard⟩ := minimum_cover_has_equal_matching hC hmin
  have hupper : A.card + B.card ≤ M.card := by
    rw [← hNcard]
    exact hM.2 N hN
  have hcard : A.card + B.card = M.card :=
    Nat.le_antisymm hupper (matching_card_le_cover_card hM.1 hC)
  refine ⟨A, B, hC, hcard, ?_, ?_⟩
  · intro l hl
    by_contra h
    have hreplace : IsVertexCover E (A.erase l) B := by
      intro x r hxr
      rcases hC x r hxr with hx | hr
      · left
        refine Finset.mem_erase.mpr ⟨?_, hx⟩
        intro hxl
        subst x
        exact h ⟨r, hxr⟩
      · exact Or.inr hr
    have hbound := hmin (A.erase l) B hreplace
    have herase := Finset.card_erase_add_one hl
    omega
  · intro r hr
    by_contra h
    have hreplace : IsVertexCover E A (B.erase r) := by
      intro l y hly
      rcases hC l y hly with hl | hy
      · exact Or.inl hl
      · right
        refine Finset.mem_erase.mpr ⟨?_, hy⟩
        intro hyr
        subst y
        exact h ⟨l, hly⟩
    have hbound := hmin A (B.erase r) hreplace
    have herase := Finset.card_erase_add_one hr
    omega

end SeymourSecondNeighborhood.Bipartite

end OAI
