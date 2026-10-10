import OAI.Combinatorics.Ryser.Geometry.ProjectiveJoins
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem card_linePoints_inter_le_one {l m : AffineLine F} (hlm : l ≠ m) :
    (linePoints l ∩ linePoints m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  exact eq_of_common_incidence_of_ne_lines hlm
    ((mem_linePoints _ _).mp (Finset.mem_inter.mp hx).1)
    ((mem_linePoints _ _).mp (Finset.mem_inter.mp hx).2)
    ((mem_linePoints _ _).mp (Finset.mem_inter.mp hy).1)
    ((mem_linePoints _ _).mp (Finset.mem_inter.mp hy).2)

theorem covered_points_on_missing_pencil_line
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (ell : AffineLine F)
    (hcover : ∀ x ∈ X, ∃ l ∈ L, Incidence x l)
    (hpell : ProjectiveIncidence p (some ell)) (hell : ell ∉ L) :
    (X ∩ linePoints ell).card ≤ 1 + (L \ affinePencil p).card := by
  classical
  let T := X ∩ linePoints ell
  let A := T.filter fun x => Sum.inl x = p
  let R := L \ affinePencil p
  have hA : A.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact Sum.inl.inj ((Finset.mem_filter.mp hx).2.trans
      (Finset.mem_filter.mp hy).2.symm)
  have hintersection : ∀ m ∈ R, (T ∩ linePoints m).card ≤ 1 := by
    intro m hm
    have hmL : m ∈ L := (Finset.mem_sdiff.mp hm).1
    have hne : ell ≠ m := fun heq => hell (heq.symm ▸ hmL)
    apply le_trans (Finset.card_le_card ?_) (card_linePoints_inter_le_one hne)
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2,
        (Finset.mem_inter.mp hx).2⟩
  have hsub : T ⊆ A ∪ R.biUnion (fun m => T ∩ linePoints m) := by
    intro x hx
    have hxX : x ∈ X := (Finset.mem_inter.mp hx).1
    have hxell : Incidence x ell :=
      (mem_linePoints _ _).mp (Finset.mem_inter.mp hx).2
    obtain ⟨m, hmL, hxm⟩ := hcover x hxX
    by_cases hmp : m ∈ affinePencil p
    · have hxp : Sum.inl x = p := by
        by_contra hne
        have heq : ell = m := eq_affineLine_of_common_projective_incidence
          hne hxell hpell hxm ((mem_affinePencil _ _).mp hmp)
        exact hell (heq.symm ▸ hmL)
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hxp⟩)
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr
        ⟨m, Finset.mem_sdiff.mpr ⟨hmL, hmp⟩,
          Finset.mem_inter.mpr ⟨hx, (mem_linePoints _ _).mpr hxm⟩⟩
  calc
    (X ∩ linePoints ell).card = T.card := rfl
    _ ≤ (A ∪ R.biUnion (fun m => T ∩ linePoints m)).card :=
      Finset.card_le_card hsub
    _ ≤ A.card + (R.biUnion (fun m => T ∩ linePoints m)).card := Finset.card_union_le _ _
    _ ≤ 1 + ∑ m ∈ R, (T ∩ linePoints m).card :=
      Nat.add_le_add hA Finset.card_biUnion_le
    _ ≤ 1 + ∑ _m ∈ R, 1 := Nat.add_le_add_left (Finset.sum_le_sum hintersection) 1
    _ = 1 + (L \ affinePencil p).card := by simp [R]

theorem mem_cover_of_pencil_survivors
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (ell : AffineLine F)
    (hcover : ∀ x ∈ X, ∃ l ∈ L, Incidence x l)
    (hpell : ProjectiveIncidence p (some ell))
    (hmany : 1 + (L \ affinePencil p).card < (X ∩ linePoints ell).card) :
    ell ∈ L := by
  by_contra hell
  exact (not_le_of_gt hmany)
    (covered_points_on_missing_pencil_line X L p ell hcover hpell hell)

end RyserCoveringCounterexample.Construction

end OAI
