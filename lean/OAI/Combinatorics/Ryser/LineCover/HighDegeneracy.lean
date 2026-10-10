import OAI.Combinatorics.Ryser.LineCover.HighSamples
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

def highParallelLines (L : Finset (AffineLine F)) (p : ProjectivePoint F) {t : ℕ}
    (b : Fin t ↪ ComplementPopulation L p) : Finset (PencilPopulation L p) :=
  Finset.univ.biUnion fun j => Finset.univ.filter fun k => k.val.1 = (b j).val.1

def highCollisionLines (L : Finset (AffineLine F)) (p : ProjectivePoint F) {t : ℕ}
    (b : Fin t ↪ ComplementPopulation L p) : Finset (PencilPopulation L p) :=
  Finset.univ.biUnion fun ij : Fin t × Fin t => Finset.univ.filter fun k =>
    ij.1 ≠ ij.2 ∧ ∃ x : ProjectivePoint F,
      ProjectiveIncidence x (some k.val) ∧
      ProjectiveIncidence x (some (b ij.1).val) ∧
      ProjectiveIncidence x (some (b ij.2).val)

def highBadLines (L : Finset (AffineLine F)) (p : ProjectivePoint F) {t : ℕ}
    (b : Fin t ↪ ComplementPopulation L p) : Finset (PencilPopulation L p) :=
  highParallelLines L p b ∪ highCollisionLines L p b

@[simp] theorem mem_highParallelLines (L : Finset (AffineLine F))
    (p : ProjectivePoint F) {t : ℕ} (b : Fin t ↪ ComplementPopulation L p)
    (k : PencilPopulation L p) :
    k ∈ highParallelLines L p b ↔ ∃ j, k.val.1 = (b j).val.1 := let _ := instFintypeF; by
  simp only [highParallelLines, Finset.mem_biUnion, Finset.mem_univ,
    Finset.mem_filter, true_and]

@[simp] theorem mem_highCollisionLines (L : Finset (AffineLine F))
    (p : ProjectivePoint F) {t : ℕ} (b : Fin t ↪ ComplementPopulation L p)
    (k : PencilPopulation L p) :
    k ∈ highCollisionLines L p b ↔ ∃ i j, i ≠ j ∧
      ∃ x : ProjectivePoint F, ProjectiveIncidence x (some k.val) ∧
        ProjectiveIncidence x (some (b i).val) ∧
        ProjectiveIncidence x (some (b j).val) := by
  simp only [highCollisionLines, Finset.mem_biUnion, Finset.mem_univ,
    Finset.mem_filter, true_and, Prod.exists]

theorem highParallelLines_card_le (L : Finset (AffineLine F))
    (p : ProjectivePoint F) {t : ℕ} (b : Fin t ↪ ComplementPopulation L p) :
    (highParallelLines L p b).card ≤ t := by
  have hone (j : Fin t) :
      (Finset.univ.filter fun k : PencilPopulation L p => k.val.1 = (b j).val.1).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro k hk k' hk'
    have hd := (Finset.mem_filter.mp hk).2
    have hd' := (Finset.mem_filter.mp hk').2
    cases p with
    | inl x =>
      apply Subtype.ext
      exact line_eq_of_direction_eq_of_incidence (hd.trans hd'.symm)
        (pencilPopulation_incident L (Sum.inl x) k)
        (pencilPopulation_incident L (Sum.inl x) k')
    | inr d =>
      have hkdir : d = k.val.1 := pencilPopulation_incident L (Sum.inr d) k
      exact (complementPopulation_not_incident L (Sum.inr d) (b j)
        (hkdir.trans hd)).elim
  calc
    _ ≤ ∑ j : Fin t,
        (Finset.univ.filter fun k : PencilPopulation L p => k.val.1 = (b j).val.1).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin t, 1 := Finset.sum_le_sum (fun j _ => hone j)
    _ = t := by simp

theorem highParallelLines_infinite_empty (L : Finset (AffineLine F))
    (d : Direction F) {t : ℕ} (b : Fin t ↪ ComplementPopulation L (Sum.inr d)) :
    highParallelLines L (Sum.inr d) b = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  obtain ⟨j, hj⟩ := (mem_highParallelLines L (Sum.inr d) b k).mp hk
  have hkdir : d = k.val.1 := pencilPopulation_incident L (Sum.inr d) k
  exact complementPopulation_not_incident L (Sum.inr d) (b j) (hkdir.trans hj)

theorem highCollisionLines_card_le (L : Finset (AffineLine F))
    (p : ProjectivePoint F) {t : ℕ} (b : Fin t ↪ ComplementPopulation L p) :
    (highCollisionLines L p b).card ≤ t * t := by
  have hone (ij : Fin t × Fin t) :
      (Finset.univ.filter fun k : PencilPopulation L p => ij.1 ≠ ij.2 ∧
        ∃ x : ProjectivePoint F, ProjectiveIncidence x (some k.val) ∧
          ProjectiveIncidence x (some (b ij.1).val) ∧
          ProjectiveIncidence x (some (b ij.2).val)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro k hk k' hk'
    obtain ⟨hij, x, hxk, hxc, hxc'⟩ := (Finset.mem_filter.mp hk).2
    obtain ⟨_, y, hyk, hyc, hyc'⟩ := (Finset.mem_filter.mp hk').2
    have hlines : (b ij.1).val ≠ (b ij.2).val := by
      intro he
      exact hij (b.injective (Subtype.ext he))
    have hxy : x = y := eq_projectivePoint_of_common_incidence
      (fun he => hlines (Option.some.inj he)) hxc hxc' hyc hyc'
    subst y
    have hxp : x ≠ p := ne_of_projectiveIncidence_of_not_projectiveIncidence
      hxc (complementPopulation_not_incident L p (b ij.1))
    apply Subtype.ext
    exact eq_affineLine_of_common_projective_incidence hxp.symm
      (pencilPopulation_incident L p k) hxk
      (pencilPopulation_incident L p k') hyk
  calc
    _ ≤ ∑ ij : Fin t × Fin t,
        (Finset.univ.filter fun k : PencilPopulation L p => ij.1 ≠ ij.2 ∧
          ∃ x : ProjectivePoint F, ProjectiveIncidence x (some k.val) ∧
            ProjectiveIncidence x (some (b ij.1).val) ∧
            ProjectiveIncidence x (some (b ij.2).val)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ij : Fin t × Fin t, 1 := Finset.sum_le_sum (fun ij _ => hone ij)
    _ = t * t := by simp

theorem highBadLines_card_le (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (b : Fin t ↪ ComplementPopulation L p) :
    (highBadLines L p b).card ≤ t + t * t :=
  (Finset.card_union_le (highParallelLines L p b) (highCollisionLines L p b)).trans (Nat.add_le_add
    (highParallelLines_card_le L p b) (highCollisionLines_card_le L p b))

theorem highTuple_grid_of_avoids (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (s : HighSample L p t)
    (havoid : ∀ i, s.1 i ∉ highBadLines L p s.2) :
    FiniteCrossings (highTuple L p s) ∧ (crossPoints (highTuple L p s)).card = t * t := by
  have hfinite (i j : Fin t) :
      ∃ x, Incidence x (s.1 i).val ∧ Incidence x (s.2 j).val := by
    have hdir : (s.1 i).val.1 ≠ (s.2 j).val.1 := by
      intro he
      apply havoid i
      exact Finset.mem_union_left _
        ((mem_highParallelLines L p s.2 (s.1 i)).mpr ⟨j, he⟩)
    exact (existsUnique_incident_of_ne_direction _ _ hdir).exists
  let f : Fin t × Fin t → Point F := fun ij => Classical.choose (hfinite ij.1 ij.2)
  have hf (ij : Fin t × Fin t) :
      Incidence (f ij) (s.1 ij.1).val ∧ Incidence (f ij) (s.2 ij.2).val :=
    Classical.choose_spec (hfinite ij.1 ij.2)
  have hinj : Function.Injective f := by
    intro ij kl he
    have hkl := hf kl
    rw [← he] at hkl
    have hxp : (Sum.inl (f ij) : ProjectivePoint F) ≠ p :=
      ne_of_projectiveIncidence_of_not_projectiveIncidence
        (l := some (s.2 ij.2).val)
        (hf ij).2 (complementPopulation_not_incident L p (s.2 ij.2))
    have hfirst : ij.1 = kl.1 := by
      apply s.1.injective
      apply Subtype.ext
      exact eq_affineLine_of_common_projective_incidence hxp.symm
        (pencilPopulation_incident L p (s.1 ij.1)) (hf ij).1
        (pencilPopulation_incident L p (s.1 kl.1)) hkl.1
    have hsecond : ij.2 = kl.2 := by
      by_contra hne
      apply havoid ij.1
      apply Finset.mem_union_right
      apply (mem_highCollisionLines L p s.2 (s.1 ij.1)).mpr
      exact ⟨ij.2, kl.2, hne, Sum.inl (f ij), (hf ij).1, (hf ij).2, hkl.2⟩
    exact Prod.ext hfirst hsecond
  have hset : crossPoints (highTuple L p s) = Finset.univ.image f := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, j, hi, hj⟩ := (mem_crossPoints (highTuple L p s) x).mp hx
      have he : f (i, j) = x := eq_of_common_incidence_of_ne_lines
        (pencil_ne_complement L p (s.1 i) (s.2 j))
        (hf (i, j)).1 (hf (i, j)).2 hi hj
      exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, he⟩
    · intro hx
      obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hx
      exact (mem_crossPoints (highTuple L p s) (f ij)).mpr
        ⟨ij.1, ij.2, (hf ij).1, (hf ij).2⟩
  refine ⟨hfinite, ?_⟩
  rw [hset, Finset.card_image_of_injective _ hinj]
  simp

end RyserCoveringCounterexample.LineCover

end

end OAI
