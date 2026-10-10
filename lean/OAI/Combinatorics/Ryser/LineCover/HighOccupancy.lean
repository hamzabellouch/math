import OAI.Combinatorics.Ryser.LineCover.HighSamples
import OAI.Combinatorics.Ryser.LineCover.DisjointPairs

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem highShapePairs_matching_of_large
    (S : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (D h : ℕ) {t : ℕ} (s : HighSample L p t)
    (hsparse : ∀ l : AffineLine F, S ≠ linePoints l → (S ∩ linePoints l).card ≤ D)
    (hnot : S ∉ tupleShapes (highTuple L p s))
    (hlarge : 2 * D * h < (S ∩ crossPoints (highTuple L p s)).card) :
    ∃ i j : Fin h ↪ Fin t, ∀ k,
      (s.1 (i k), s.2 (j k)) ∈ highShapePairs S L p := by
  let P := S ∩ crossPoints (highTuple L p s)
  have hex (x : ↥P) : ∃ ij : Fin t × Fin t,
      Incidence x.val (s.1 ij.1).val ∧ Incidence x.val (s.2 ij.2).val := by
    obtain ⟨i, j, hi, hj⟩ :=
      (mem_crossPoints (highTuple L p s) x.val).mp (Finset.mem_inter.mp x.property).2
    exact ⟨(i, j), hi, hj⟩
  let rep : ↥P → Fin t × Fin t := fun x => Classical.choose (hex x)
  have hrep (x : ↥P) :
      Incidence x.val (s.1 (rep x).1).val ∧ Incidence x.val (s.2 (rep x).2).val :=
    Classical.choose_spec (hex x)
  have hnotleft (i : Fin t) : S ≠ linePoints (s.1 i).val := by
    intro he
    exact hnot ((mem_tupleShapes (highTuple L p s) S).mpr ⟨Sum.inl i, he.symm⟩)
  have hnotright (j : Fin t) : S ≠ linePoints (s.2 j).val := by
    intro he
    exact hnot ((mem_tupleShapes (highTuple L p s) S).mpr ⟨Sum.inr j, he.symm⟩)
  have hleft (i : Fin t) :
      (Finset.univ.filter fun x : ↥P => (rep x).1 = i).card ≤ D := by
    calc
      _ ≤ (S ∩ linePoints (s.1 i).val).card := by
        apply Finset.card_le_card_of_injOn (fun x : ↥P => x.val)
        · intro x hx
          have hxi := (Finset.mem_filter.mp hx).2
          refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp x.property).1, ?_⟩
          apply (mem_linePoints x.val (s.1 i).val).mpr
          simpa only [hxi] using (hrep x).1
        · intro x _ y _ hxy
          exact Subtype.ext hxy
      _ ≤ D := hsparse _ (hnotleft i)
  have hright (j : Fin t) :
      (Finset.univ.filter fun x : ↥P => (rep x).2 = j).card ≤ D := by
    calc
      _ ≤ (S ∩ linePoints (s.2 j).val).card := by
        apply Finset.card_le_card_of_injOn (fun x : ↥P => x.val)
        · intro x hx
          have hxj := (Finset.mem_filter.mp hx).2
          refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp x.property).1, ?_⟩
          apply (mem_linePoints x.val (s.2 j).val).mpr
          simpa only [hxj] using (hrep x).2
        · intro x _ y _ hxy
          exact Subtype.ext hxy
      _ ≤ D := hsparse _ (hnotright j)
  obtain ⟨e, hei, hej⟩ := exists_disjoint_coordinate_sample
    (Finset.univ : Finset ↥P) (fun x => (rep x).1) (fun x => (rep x).2)
    D h hleft hright (by simpa only [Finset.card_univ, Fintype.card_coe] using hlarge)
  let i : Fin h ↪ Fin t := ⟨fun k => (rep (e k).val).1, hei⟩
  let j : Fin h ↪ Fin t := ⟨fun k => (rep (e k).val).2, hej⟩
  refine ⟨i, j, ?_⟩
  intro k
  apply (mem_highShapePairs S L p (s.1 (i k), s.2 (j k))).mpr
  refine ⟨?_, hnotleft (i k), hnotright (j k)⟩
  exact ⟨(e k).val.val, (Finset.mem_inter.mp (e k).val.property).1,
    (hrep (e k).val).1, (hrep (e k).val).2⟩

theorem highSurvivorPoints_card_le
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (s : HighSample L p t) :
    (X ∩ crossPoints (highTuple L p s)).card ≤ highSurvivorPairCount X L p s := by
  let P := X ∩ crossPoints (highTuple L p s)
  let Q := Finset.univ.filter fun ij : Fin t × Fin t =>
    (s.1 ij.1, s.2 ij.2) ∈ highCrossPairs X L p
  have hex (x : ↥P) : ∃ ij : Fin t × Fin t,
      Incidence x.val (s.1 ij.1).val ∧ Incidence x.val (s.2 ij.2).val := by
    obtain ⟨i, j, hi, hj⟩ :=
      (mem_crossPoints (highTuple L p s) x.val).mp (Finset.mem_inter.mp x.property).2
    exact ⟨(i, j), hi, hj⟩
  let rep : ↥P → Fin t × Fin t := fun x => Classical.choose (hex x)
  have hrep (x : ↥P) :
      Incidence x.val (s.1 (rep x).1).val ∧ Incidence x.val (s.2 (rep x).2).val :=
    Classical.choose_spec (hex x)
  let enc : ↥P → ↥Q := fun x => ⟨rep x, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (mem_highCrossPairs X L p _).mpr
      ⟨x.val, (Finset.mem_inter.mp x.property).1, (hrep x).1, (hrep x).2⟩⟩⟩
  have hinj : Function.Injective enc := by
    intro x y hxy
    have he : rep x = rep y := congrArg Subtype.val hxy
    have hy := hrep y
    rw [← he] at hy
    apply Subtype.ext
    exact eq_of_common_incidence_of_ne_lines
      (pencil_ne_complement L p (s.1 (rep x).1) (s.2 (rep x).2))
      (hrep x).1 (hrep x).2 hy.1 hy.2
  exact Finset.card_le_card_of_injective hinj

end RyserCoveringCounterexample.LineCover

end

end OAI
