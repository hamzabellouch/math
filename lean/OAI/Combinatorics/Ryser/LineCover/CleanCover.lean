import OAI.Combinatorics.Ryser.LineCover.Process
import OAI.Combinatorics.Ryser.LineCover.Overlap

namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n : ℕ}

def cleanLines (ω : Fin n → Outcome shapes D) (L : Finset (AffineLine F)) :
    Finset (AffineLine F) := L.filter fun l => linePoints l ∉ selected ω

theorem cleanLines_subset (ω : Fin n → Outcome shapes D) (L : Finset (AffineLine F)) :
    cleanLines ω L ⊆ L := Finset.filter_subset _ _

theorem cleanLines_not_selected {ω : Fin n → Outcome shapes D}
    {L : Finset (AffineLine F)} {l : AffineLine F} (hl : l ∈ cleanLines ω L) :
    linePoints l ∉ selected ω := (Finset.mem_filter.mp hl).2

theorem survivor_incidence_not_selected {ω : Fin n → Outcome shapes D}
    {x : Point F} {l : AffineLine F} (hx : x ∈ survivors ∅ ω)
    (hl : Incidence x l) : linePoints l ∉ selected ω := by
  intro hs
  have hactive : linePoints l ∈ selected ω \ ∅ := by simpa using hs
  exact mem_survivors_active.mp hx (linePoints l) hactive ((mem_linePoints x l).mpr hl)

theorem survivors_inter_cleanLines (ω : Fin n → Outcome shapes D)
    (L : Finset (AffineLine F)) :
    survivors ∅ ω ∩ L.biUnion linePoints =
      survivors ∅ ω ∩ (cleanLines ω L).biUnion linePoints := by
  ext x
  constructor
  · intro hx
    obtain ⟨hs, hc⟩ := Finset.mem_inter.mp hx
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_inter.mpr ⟨hs, Finset.mem_biUnion.mpr
      ⟨l, Finset.mem_filter.mpr ⟨hl, survivor_incidence_not_selected hs
        ((mem_linePoints x l).mp hxl)⟩, hxl⟩⟩
  · intro hx
    obtain ⟨hs, hc⟩ := Finset.mem_inter.mp hx
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_inter.mpr ⟨hs,
      Finset.mem_biUnion.mpr ⟨l, cleanLines_subset ω L hl, hxl⟩⟩

theorem survivors_sdiff_cleanLines (ω : Fin n → Outcome shapes D)
    (L : Finset (AffineLine F)) :
    survivors ∅ ω \ L.biUnion linePoints =
      survivors ∅ ω \ (cleanLines ω L).biUnion linePoints := by
  ext x
  constructor
  · intro hx
    obtain ⟨hs, hc⟩ := Finset.mem_sdiff.mp hx
    refine Finset.mem_sdiff.mpr ⟨hs, ?_⟩
    intro hclean
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hclean
    exact hc (Finset.mem_biUnion.mpr ⟨l, cleanLines_subset ω L hl, hxl⟩)
  · intro hx
    obtain ⟨hs, hc⟩ := Finset.mem_sdiff.mp hx
    refine Finset.mem_sdiff.mpr ⟨hs, ?_⟩
    intro horig
    have hboth := Finset.mem_inter.mpr ⟨hs, horig⟩
    rw [survivors_inter_cleanLines] at hboth
    exact hc (Finset.mem_inter.mp hboth).2

theorem coverPencil_mono {L K : Finset (AffineLine F)} (h : L ⊆ K)
    (p : ProjectivePoint F) : coverPencil L p ⊆ coverPencil K p := by
  intro l hl
  obtain ⟨hL, hi⟩ := (mem_coverPencil L p l).mp hl
  exact (mem_coverPencil K p l).mpr ⟨h hL, hi⟩

theorem coveredPoints_eq_inter_biUnion (X : Finset (Point F))
    (L : Finset (AffineLine F)) :
    coveredPoints Incidence X L = X ∩ L.biUnion linePoints := by
  ext x
  change x ∈ X.filter (fun x => 0 < multiplicity Incidence L x) ↔ _
  rw [Finset.mem_filter, Finset.mem_inter]
  unfold multiplicity
  have hfilter :
      @Finset.filter _ (Incidence x) (fun l => Classical.propDecidable (Incidence x l)) L =
        L.filter (Incidence x) := Finset.filter_congr_decidable _ _ _
  rw [hfilter]
  constructor
  · rintro ⟨hx, hn⟩
    obtain ⟨l, hl⟩ := Finset.card_pos.mp hn
    obtain ⟨hL, hi⟩ := Finset.mem_filter.mp hl
    exact ⟨hx, Finset.mem_biUnion.mpr ⟨l, hL, (mem_linePoints x l).mpr hi⟩⟩
  · rintro ⟨hx, hl⟩
    obtain ⟨l, hL, hi⟩ := Finset.mem_biUnion.mp hl
    exact ⟨hx, Finset.card_pos.mpr ⟨l,
      Finset.mem_filter.mpr ⟨hL, (mem_linePoints x l).mp hi⟩⟩⟩

theorem survivors_ignore_tuple_eq {t : ℕ} (ω : Fin n → Outcome shapes D)
    (a : LineTuple F t) (ha : ∀ i, linePoints (a i) ∉ selected ω) :
    survivors (tupleShapes a) ω = survivors ∅ ω := by
  have hd : selected ω \ tupleShapes a = selected ω := by
    ext S
    simp only [Finset.mem_sdiff]
    constructor
    · exact And.left
    · intro hs
      refine ⟨hs, ?_⟩
      intro ht
      obtain ⟨i, rfl⟩ := (mem_tupleShapes a S).mp ht
      exact ha i hs
  ext x
  rw [mem_survivors_active, mem_survivors_active, hd, Finset.sdiff_empty]

end RyserCoveringCounterexample.LineCover

end

end OAI
