import OAI.Combinatorics.SecondNeighborhood.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

variable {V : Type*}

def Conflict (r : V → V → Prop) (a b : V × V) : Prop :=
  r a.1 b.1 ∧ r b.2 a.2

def LeftCovers (r : V → V → Prop) (a z : V × V) : Prop :=
  a.2 = z.2 ∧ r a.1 z.1

def RightCovers (r : V → V → Prop) (b z : V × V) : Prop :=
  b.1 = z.1 ∧ r b.2 z.2

variable [Fintype V] [DecidableEq V]

noncomputable section

def leftImage (r : V → V → Prop) (R : Finset (V × V)) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun z => ∃ p, (p, z.2) ∈ R ∧ r p z.1)

def rightImage (r : V → V → Prop) (C : Finset (V × V)) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun z => ∃ s, (z.1, s) ∈ C ∧ r s z.2)

def Covered (r : V → V → Prop) (R C : Finset (V × V)) (z : V × V) : Prop :=
  z ∈ leftImage r R ∨ z ∈ rightImage r C

def Z (r : V → V → Prop) (R C : Finset (V × V)) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun z =>
    ∃ p s, (p, z.2) ∈ R ∧ (z.1, s) ∈ C ∧ r p z.1 ∧ r s z.2)

def H (r : V → V → Prop) (R C : Finset (V × V)) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun h =>
    ∃ i j, (h.1, j) ∈ R ∧ (i, h.2) ∈ C ∧ r h.1 i ∧ r h.2 j)

def ConflictFree (r : V → V → Prop) (R C : Finset (V × V)) : Prop :=
  ∀ a ∈ R, ∀ b ∈ C, ¬ Conflict r a b

def uncoveredZ (r : V → V → Prop) (R C R' C' : Finset (V × V)) :
    Finset (V × V) := by
  classical
  exact (Z r R C).filter (fun z => ¬ Covered r R' C' z)

structure PruningResult (r : V → V → Prop) (R C R' C' : Finset (V × V)) : Prop where
  subset_left : R' ⊆ R
  subset_right : C' ⊆ C
  no_conflicts : ConflictFree r R' C'
  retain_left : ∀ a ∈ R, (∀ b ∈ C, ¬ Conflict r a b) → a ∈ R'
  retain_right : ∀ b ∈ C, (∀ a ∈ R, ¬ Conflict r a b) → b ∈ C'
  deletion_bound : (R \ R').card + (C \ C').card ≤
    (H r R C).card + (uncoveredZ r R C R' C').card

def PruningStatement (r : V → V → Prop) : Prop :=
  ∀ R C : Finset (V × V), ∃ R' C', PruningResult r R C R' C'

@[simp] theorem mem_leftImage {r : V → V → Prop} {R : Finset (V × V)}
    {z : V × V} : z ∈ leftImage r R ↔ ∃ p, (p, z.2) ∈ R ∧ r p z.1 := by
  classical
  simp [leftImage]

@[simp] theorem mem_rightImage {r : V → V → Prop} {C : Finset (V × V)}
    {z : V × V} : z ∈ rightImage r C ↔ ∃ s, (z.1, s) ∈ C ∧ r s z.2 := by
  classical
  simp [rightImage]

@[simp] theorem mem_Z {r : V → V → Prop} {R C : Finset (V × V)} {z : V × V} :
    z ∈ Z r R C ↔
      ∃ p s, (p, z.2) ∈ R ∧ (z.1, s) ∈ C ∧ r p z.1 ∧ r s z.2 := by
  classical
  simp [Z]

@[simp] theorem mem_H {r : V → V → Prop} {R C : Finset (V × V)} {h : V × V} :
    h ∈ H r R C ↔
      ∃ i j, (h.1, j) ∈ R ∧ (i, h.2) ∈ C ∧ r h.1 i ∧ r h.2 j := by
  classical
  simp [H]

@[simp] theorem mem_uncoveredZ {r : V → V → Prop}
    {R C R' C' : Finset (V × V)} {z : V × V} :
    z ∈ uncoveredZ r R C R' C' ↔ z ∈ Z r R C ∧ ¬ Covered r R' C' z := by
  classical
  simp only [uncoveredZ, Finset.mem_filter]

theorem exists_leftCovers_iff {r : V → V → Prop} {R : Finset (V × V)}
    {z : V × V} : (∃ a ∈ R, LeftCovers r a z) ↔ z ∈ leftImage r R := by
  constructor
  · rintro ⟨⟨p, j⟩, ha, hj, hpi⟩
    apply mem_leftImage.mpr
    refine ⟨p, ?_, hpi⟩
    change j = z.2 at hj
    simpa only [hj] using ha
  · intro hz
    obtain ⟨p, hp, hpi⟩ := mem_leftImage.mp hz
    exact ⟨(p, z.2), hp, rfl, hpi⟩

theorem exists_rightCovers_iff {r : V → V → Prop} {C : Finset (V × V)}
    {z : V × V} : (∃ b ∈ C, RightCovers r b z) ↔ z ∈ rightImage r C := by
  constructor
  · rintro ⟨⟨i, s⟩, hb, hi, hsj⟩
    apply mem_rightImage.mpr
    refine ⟨s, ?_, hsj⟩
    change i = z.1 at hi
    simpa only [hi] using hb
  · intro hz
    obtain ⟨s, hs, hsj⟩ := mem_rightImage.mp hz
    exact ⟨(z.1, s), hs, rfl, hsj⟩

@[simp] theorem leftImage_empty (r : V → V → Prop) : leftImage r ∅ = ∅ := by
  classical
  ext z
  simp

@[simp] theorem rightImage_empty (r : V → V → Prop) : rightImage r ∅ = ∅ := by
  classical
  ext z
  simp

theorem leftImage_mono (r : V → V → Prop) {R R' : Finset (V × V)}
    (h : R ⊆ R') : leftImage r R ⊆ leftImage r R' := by
  intro z hz
  obtain ⟨p, hp, hpz⟩ := mem_leftImage.mp hz
  exact mem_leftImage.mpr ⟨p, h hp, hpz⟩

theorem rightImage_mono (r : V → V → Prop) {C C' : Finset (V × V)}
    (h : C ⊆ C') : rightImage r C ⊆ rightImage r C' := by
  intro z hz
  obtain ⟨s, hs, hsz⟩ := mem_rightImage.mp hz
  exact mem_rightImage.mpr ⟨s, h hs, hsz⟩

theorem Covered.mono {r : V → V → Prop} {R C R' C' : Finset (V × V)}
    (hR : R ⊆ R') (hC : C ⊆ C') {z : V × V}
    (h : Covered r R C z) : Covered r R' C' z := by
  rcases h with h | h
  · exact Or.inl (leftImage_mono r hR h)
  · exact Or.inr (rightImage_mono r hC h)

theorem Z_eq_inter (r : V → V → Prop) (R C : Finset (V × V)) :
    Z r R C = leftImage r R ∩ rightImage r C := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨p, s, hp, hs, hpi, hsj⟩ := mem_Z.mp hz
    exact Finset.mem_inter.mpr
      ⟨mem_leftImage.mpr ⟨p, hp, hpi⟩, mem_rightImage.mpr ⟨s, hs, hsj⟩⟩
  · intro hz
    obtain ⟨hl, hr⟩ := Finset.mem_inter.mp hz
    obtain ⟨p, hp, hpi⟩ := mem_leftImage.mp hl
    obtain ⟨s, hs, hsj⟩ := mem_rightImage.mp hr
    exact mem_Z.mpr ⟨p, s, hp, hs, hpi, hsj⟩

theorem conflict_corner_mem_Z {r : V → V → Prop} {R C : Finset (V × V)}
    {a b : V × V} (ha : a ∈ R) (hb : b ∈ C) (hc : Conflict r a b) :
    (b.1, a.2) ∈ Z r R C := by
  exact mem_Z.mpr ⟨a.1, b.2, by simpa using ha, by simpa using hb, hc.1, hc.2⟩

theorem conflict_corner_mem_H {r : V → V → Prop} {R C : Finset (V × V)}
    {a b : V × V} (ha : a ∈ R) (hb : b ∈ C) (hc : Conflict r a b) :
    (a.1, b.2) ∈ H r R C := by
  exact mem_H.mpr ⟨b.1, a.2, by simpa using ha, by simpa using hb, hc.1, hc.2⟩

theorem conflictFree_iff_disjoint {r : V → V → Prop} {R C : Finset (V × V)} :
    ConflictFree r R C ↔ Disjoint (leftImage r R) (rightImage r C) := by
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro z hl hr
    obtain ⟨p, hp, hpi⟩ := mem_leftImage.mp hl
    obtain ⟨s, hs, hsj⟩ := mem_rightImage.mp hr
    exact h (p, z.2) hp (z.1, s) hs ⟨hpi, hsj⟩
  · intro h a ha b hb hc
    have hl : (b.1, a.2) ∈ leftImage r R :=
      mem_leftImage.mpr ⟨a.1, by simpa using ha, hc.1⟩
    have hr : (b.1, a.2) ∈ rightImage r C :=
      mem_rightImage.mpr ⟨b.2, by simpa using hb, hc.2⟩
    exact Finset.disjoint_left.mp h hl hr

omit [Fintype V] [DecidableEq V] in
theorem ConflictFree.mono {r : V → V → Prop} {R C R' C' : Finset (V × V)}
    (h : ConflictFree r R C) (hR : R' ⊆ R) (hC : C' ⊆ C) :
    ConflictFree r R' C' := by
  intro a ha b hb
  exact h a (hR ha) b (hC hb)

theorem Z_eq_empty_of_conflictFree {r : V → V → Prop} {R C : Finset (V × V)}
    (h : ConflictFree r R C) : Z r R C = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨p, s, hp, hs, hpi, hsj⟩ := mem_Z.mp hz
  exact h (p, z.2) hp (z.1, s) hs ⟨hpi, hsj⟩

theorem H_eq_empty_of_conflictFree {r : V → V → Prop} {R C : Finset (V × V)}
    (h : ConflictFree r R C) : H r R C = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨i, j, hp, hs, hpi, hsj⟩ := mem_H.mp hz
  exact h (z.1, j) hp (i, z.2) hs ⟨hpi, hsj⟩

theorem conflictFree_left_not_covers_Z {r : V → V → Prop}
    {R C : Finset (V × V)} {a z : V × V}
    (ha : ∀ b ∈ C, ¬ Conflict r a b) (hz : z ∈ Z r R C) :
    ¬ LeftCovers r a z := by
  intro hc
  obtain ⟨p, s, _, hs, _, hsj⟩ := mem_Z.mp hz
  apply ha (z.1, s) hs
  refine ⟨hc.2, ?_⟩
  simpa only [hc.1] using hsj

theorem conflictFree_right_not_covers_Z {r : V → V → Prop}
    {R C : Finset (V × V)} {b z : V × V}
    (hb : ∀ a ∈ R, ¬ Conflict r a b) (hz : z ∈ Z r R C) :
    ¬ RightCovers r b z := by
  intro hc
  obtain ⟨p, s, hp, _, hpi, _⟩ := mem_Z.mp hz
  apply hb (p, z.2) hp
  refine ⟨?_, hc.2⟩
  simpa only [hc.1] using hpi

theorem uncoveredZ_eq_sdiff (r : V → V → Prop) (R C R' C' : Finset (V × V)) :
    uncoveredZ r R C R' C' = Z r R C \ (leftImage r R' ∪ rightImage r C') := by
  classical
  ext z
  simp only [mem_uncoveredZ, Finset.mem_sdiff, Finset.mem_union, Covered]

theorem pruningResult_self {r : V → V → Prop} {R C : Finset (V × V)}
    (h : ConflictFree r R C) : PruningResult r R C R C where
  subset_left := fun _ ha => ha
  subset_right := fun _ hb => hb
  no_conflicts := h
  retain_left := fun _ ha _ => ha
  retain_right := fun _ hb _ => hb
  deletion_bound := by simp

theorem exists_pruning_of_conflictFree {r : V → V → Prop} {R C : Finset (V × V)}
    (h : ConflictFree r R C) : ∃ R' C', PruningResult r R C R' C' :=
  ⟨R, C, pruningResult_self h⟩

end
end SeymourSecondNeighborhood.Pruning

end OAI
