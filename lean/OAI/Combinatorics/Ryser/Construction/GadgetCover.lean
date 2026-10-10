import OAI.Combinatorics.Ryser.Construction.CoverPencil
import OAI.Combinatorics.Ryser.Geometry.Cardinality
import Lean.Elab.Tactic.Omega

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem mixed_covered_points_on_missing_pencil_line
    (X B : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (ell : AffineLine F)
    (hcover : ∀ x ∈ X, x ∈ B ∨ ∃ l ∈ L, Incidence x l)
    (hpell : ProjectiveIncidence p (some ell)) (hell : ell ∉ L) :
    (X ∩ linePoints ell).card ≤ 1 + (L \ affinePencil p).card + B.card := by
  have hlinecover : ∀ x ∈ X \ B, ∃ l ∈ L, Incidence x l := by
    intro x hx
    rcases hcover x (Finset.mem_sdiff.mp hx).1 with hxB | hxL
    · exact ((Finset.mem_sdiff.mp hx).2 hxB).elim
    · exact hxL
  have hbound := covered_points_on_missing_pencil_line (X \ B) L p ell
    hlinecover hpell hell
  have hsub : X ∩ linePoints ell ⊆ ((X \ B) ∩ linePoints ell) ∪ B := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_right _ hxB
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).1, hxB⟩,
          (Finset.mem_inter.mp hx).2⟩)
  calc
    (X ∩ linePoints ell).card ≤ (((X \ B) ∩ linePoints ell) ∪ B).card :=
      Finset.card_le_card hsub
    _ ≤ ((X \ B) ∩ linePoints ell).card + B.card := Finset.card_union_le _ _
    _ ≤ 1 + (L \ affinePencil p).card + B.card := Nat.add_le_add_right hbound _

theorem mixed_cover_eq_parallel_of_near_pencil
    (Y B : Finset (Point F)) (L : Finset (AffineLine F))
    (hlarge : 200 < 19 * Fintype.card F)
    (hlines : ∀ ell : AffineLine F,
      Fintype.card F ≤ 8 * (Y ∩ linePoints ell).card)
    (hcover : ∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell)
    (hbudget : 2 * L.card + B.card ≤ 2 * Fintype.card F)
    (hnear : ∃ p : ProjectivePoint F,
      99 * Fintype.card F ≤ 100 * (L ∩ affinePencil p).card) :
    ∃ d : Direction F, L = affinePencil (Sum.inr d) ∧ B = ∅ := by
  obtain ⟨p, hp⟩ := hnear
  have hLcard : L.card ≤ Fintype.card F := by omega
  have hdecomp := Finset.card_sdiff_add_card_inter L (affinePencil p)
  have hforced : affinePencil p ⊆ L := by
    intro ell hell
    by_contra hmissing
    have hpell : ProjectiveIncidence p (some ell) :=
      (mem_affinePencil _ _).mp hell
    have hcount := mixed_covered_points_on_missing_pencil_line Y B L p ell
      hcover hpell hmissing
    have hlower := hlines ell
    omega
  cases p with
  | inl p =>
      have hcard := Finset.card_le_card hforced
      rw [card_affinePencil_finite] at hcard
      omega
  | inr d =>
      have heq : affinePencil (Sum.inr d) = L :=
        Finset.eq_of_subset_of_card_le hforced (by simpa using hLcard)
      have hL : L.card = Fintype.card F := by rw [← heq, card_affinePencil_infinite]
      have hB : B.card = 0 := by omega
      exact ⟨d, heq.symm, Finset.card_eq_zero.mp hB⟩

theorem missed_points_subset_of_mixed_cover
    (Y B : Finset (Point F)) (L : Finset (AffineLine F))
    (hcover : ∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell) :
    Y \ L.biUnion linePoints ⊆ B := by
  intro y hy
  rcases hcover y (Finset.mem_sdiff.mp hy).1 with hyB | ⟨ell, hell, hyell⟩
  · exact hyB
  · exact ((Finset.mem_sdiff.mp hy).2
      (Finset.mem_biUnion.mpr ⟨ell, hell, (mem_linePoints _ _).mpr hyell⟩)).elim

end RyserCoveringCounterexample.Construction

end OAI
