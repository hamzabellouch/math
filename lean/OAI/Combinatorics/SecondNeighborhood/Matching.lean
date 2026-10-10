import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

namespace OAI

namespace SeymourSecondNeighborhood.Bipartite

variable {L R : Type*}

def IsMatching (E : L → R → Prop) (M : Finset (L × R)) : Prop :=
  (∀ e ∈ M, E e.1 e.2) ∧
    Set.InjOn Prod.fst (M : Set (L × R)) ∧
    Set.InjOn Prod.snd (M : Set (L × R))

def IsMaximumMatching (E : L → R → Prop) (M : Finset (L × R)) : Prop :=
  IsMatching E M ∧ ∀ N, IsMatching E N → N.card ≤ M.card

def IsVertexCover (E : L → R → Prop) (A : Finset L) (B : Finset R) : Prop :=
  ∀ l r, E l r → l ∈ A ∨ r ∈ B

@[simp] theorem isMatching_empty (E : L → R → Prop) :
    IsMatching E ∅ := by
  simp [IsMatching, Set.InjOn]

theorem IsMatching.submatching {E : L → R → Prop} {M N : Finset (L × R)}
    (hM : IsMatching E M) (hNM : N ⊆ M) : IsMatching E N := by
  refine ⟨fun e he => hM.1 e (hNM he), ?_, ?_⟩
  · intro e he f hf hef
    exact hM.2.1 (hNM he) (hNM hf) hef
  · intro e he f hf hef
    exact hM.2.2 (hNM he) (hNM hf) hef

theorem IsMatching.mono_relation {E F : L → R → Prop} {M : Finset (L × R)}
    (hM : IsMatching E M) (hEF : ∀ l r, E l r → F l r) : IsMatching F M :=
  ⟨fun e he => hEF e.1 e.2 (hM.1 e he), hM.2⟩

theorem IsMatching.left_unique {E : L → R → Prop} {M : Finset (L × R)}
    (hM : IsMatching E M) {l : L} {r s : R}
    (hr : (l, r) ∈ M) (hs : (l, s) ∈ M) : r = s := by
  exact congrArg Prod.snd (hM.2.1 hr hs rfl)

theorem IsMatching.right_unique {E : L → R → Prop} {M : Finset (L × R)}
    (hM : IsMatching E M) {l k : L} {r : R}
    (hl : (l, r) ∈ M) (hk : (k, r) ∈ M) : l = k := by
  exact congrArg Prod.fst (hM.2.2 hl hk rfl)

section DecidableEq

variable [DecidableEq L] [DecidableEq R]

def leftVertices (M : Finset (L × R)) : Finset L := M.image Prod.fst

def rightVertices (M : Finset (L × R)) : Finset R := M.image Prod.snd

omit [DecidableEq R] in
@[simp] theorem mem_leftVertices {M : Finset (L × R)} {l : L} :
    l ∈ leftVertices M ↔ ∃ r, (l, r) ∈ M := by
  simp only [leftVertices, Finset.mem_image]
  constructor
  · rintro ⟨⟨k, r⟩, hkr, hkl⟩
    cases hkl
    exact ⟨r, hkr⟩
  · rintro ⟨r, hr⟩
    exact ⟨(l, r), hr, rfl⟩

omit [DecidableEq L] in
@[simp] theorem mem_rightVertices {M : Finset (L × R)} {r : R} :
    r ∈ rightVertices M ↔ ∃ l, (l, r) ∈ M := by
  simp only [rightVertices, Finset.mem_image]
  constructor
  · rintro ⟨⟨l, s⟩, hls, hsr⟩
    cases hsr
    exact ⟨l, hls⟩
  · rintro ⟨l, hl⟩
    exact ⟨(l, r), hl, rfl⟩

omit [DecidableEq R] in
theorem matching_card_leftVertices {E : L → R → Prop} {M : Finset (L × R)}
    (hM : IsMatching E M) : (leftVertices M).card = M.card :=
  Finset.card_image_iff.mpr hM.2.1

omit [DecidableEq L] in
theorem matching_card_rightVertices {E : L → R → Prop} {M : Finset (L × R)}
    (hM : IsMatching E M) : (rightVertices M).card = M.card :=
  Finset.card_image_iff.mpr hM.2.2

omit [DecidableEq R] in
theorem matching_card_le_cover_card {E : L → R → Prop}
    {M : Finset (L × R)} {A : Finset L} {B : Finset R}
    (hM : IsMatching E M) (hC : IsVertexCover E A B) :
    M.card ≤ A.card + B.card := by
  classical
  let ML := M.filter fun e => e.1 ∈ A
  let MR := M.filter fun e => e.1 ∉ A
  have hL : ML.card ≤ A.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro e he
      exact (Finset.mem_filter.mp he).2
    · intro e he f hf hef
      exact hM.2.1 (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 hef
  have hR : MR.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro e he
      rcases Finset.mem_filter.mp he with ⟨heM, heA⟩
      exact (hC e.1 e.2 (hM.1 e heM)).resolve_left heA
    · intro e he f hf hef
      exact hM.2.2 (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 hef
  calc
    M.card = ML.card + MR.card :=
      (Finset.card_filter_add_card_filter_not (s := M) (fun e => e.1 ∈ A)).symm
    _ ≤ A.card + B.card := Nat.add_le_add hL hR

end DecidableEq

section Finite

variable [Fintype L] [Fintype R]

theorem exists_maximum_matching (E : L → R → Prop) :
    ∃ M, IsMaximumMatching E M := by
  classical
  let candidates : Finset (Finset (L × R)) := Finset.univ.filter (IsMatching E)
  have hne : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates]
  obtain ⟨M, hM, hmax⟩ := candidates.exists_max_image Finset.card hne
  refine ⟨M, (Finset.mem_filter.mp hM).2, ?_⟩
  intro N hN
  exact hmax N (by simp [candidates, hN])

theorem exists_maximum_matching_min_cost (E : L → R → Prop)
    (cost : Finset (L × R) → ℕ) :
    ∃ M, IsMaximumMatching E M ∧
      ∀ N, IsMatching E N → N.card = M.card → cost M ≤ cost N := by
  classical
  obtain ⟨M₀, hM₀, hmax₀⟩ := exists_maximum_matching E
  let candidates : Finset (Finset (L × R)) :=
    Finset.univ.filter fun N => IsMatching E N ∧ N.card = M₀.card
  have hne : candidates.Nonempty := by
    refine ⟨M₀, ?_⟩
    simp [candidates, hM₀]
  obtain ⟨M, hM, hmin⟩ := candidates.exists_min_image cost hne
  have hM' : IsMatching E M ∧ M.card = M₀.card := (Finset.mem_filter.mp hM).2
  refine ⟨M, ⟨hM'.1, ?_⟩, ?_⟩
  · intro N hN
    rw [hM'.2]
    exact hmax₀ N hN
  · intro N hN hcard
    exact hmin N (by simp [candidates, hN, hcard, hM'.2])

end Finite

end SeymourSecondNeighborhood.Bipartite

end OAI
