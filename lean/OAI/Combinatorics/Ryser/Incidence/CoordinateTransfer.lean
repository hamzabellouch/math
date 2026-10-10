import OAI.Combinatorics.Ryser.Incidence.Pencils
import OAI.Combinatorics.Ryser.Incidence.CoordinateTransferSet

namespace OAI

namespace RyserCoveringCounterexample.Incidence

noncomputable section

variable {F : Type*} [Field F] [DecidableEq F]

theorem pencilSlice_image_transform (T : ProjectiveTransform F)
    (L : Finset (ProjectiveLine F)) (p : ProjectivePoint F) :
    pencilSlice (L.image T.lines) (T.points p) = (pencilSlice L p).image T.lines := by
  ext l
  constructor
  · intro hl
    obtain ⟨hl, hp⟩ := Finset.mem_filter.mp hl
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_image.mpr ⟨m,
      Finset.mem_filter.mpr ⟨hm, (T.incidence p m).mp hp⟩, rfl⟩
  · intro hl
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem T.lines hm,
      (T.incidence p m).mpr hp⟩

theorem card_pencilSlice_image_transform (T : ProjectiveTransform F)
    (L : Finset (ProjectiveLine F)) (p : ProjectivePoint F) :
    (pencilSlice (L.image T.lines) (T.points p)).card = (pencilSlice L p).card := by
  rw [pencilSlice_image_transform]
  exact Finset.card_image_of_injective _ T.lines.injective

theorem hasJoin_image_transform (T : ProjectiveTransform F)
    (L : Finset (ProjectiveLine F)) (p w : ProjectivePoint F) (z : Point F)
    (hw : T.points w = Sum.inl z)
    (hjoin : ∃ l ∈ L, ProjectiveIncidence p l ∧ ProjectiveIncidence w l) :
    HasJoin (L.image T.lines) (T.points p) z := by
  obtain ⟨l, hl, hp, hwl⟩ := hjoin
  refine ⟨T.lines l, Finset.mem_image_of_mem T.lines hl, (T.incidence p l).mpr hp, ?_⟩
  rw [← hw]
  exact (T.incidence w l).mpr hwl

theorem coordinateGraph_hasJoin (T : ProjectiveTransform F)
    (W : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
    (p : ProjectivePoint F)
    (hjoin : ∀ w ∈ W, ∃ l ∈ L,
      ProjectiveIncidence p l ∧ ProjectiveIncidence w l)
    (z : Point F) (hz : z ∈ coordinateGraph T W) :
    HasJoin (L.image T.lines) (T.points p) z := by
  obtain ⟨w, hw, hTw⟩ := (mem_coordinateGraph_iff T W z).mp hz
  exact hasJoin_image_transform T L p w z hTw
    (hjoin w (goodW_subset T W hw))

theorem coordinate_transfer
    (P W : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
    (T : ProjectiveTransform F) (p1 p2 p3 p4 : ProjectivePoint F) (H : ℝ)
    (hWP : W ⊆ P)
    (hcap : ∀ l : ProjectiveLine F,
      ((P.filter (fun p => ProjectiveIncidence p l)).card : ℝ) ≤ H)
    (hdegree : ∀ p ∈ P, ((pencilSlice L p).card : ℝ) ≤ H)
    (hp1 : p1 ∈ P) (hp2 : p2 ∈ P) (hp3 : p3 ∈ P) (hp4 : p4 ∈ P)
    (hT1 : T.points p1 = Sum.inr (some 0))
    (hT2 : T.points p2 = Sum.inr none)
    (hT3 : T.points p3 = Sum.inr (some 1))
    (hT4 : T.points p4 = Sum.inl (0, 0))
    (hjoins : ∀ w ∈ W,
      (∃ l ∈ L, ProjectiveIncidence p1 l ∧ ProjectiveIncidence w l) ∧
      (∃ l ∈ L, ProjectiveIncidence p2 l ∧ ProjectiveIncidence w l) ∧
      (∃ l ∈ L, ProjectiveIncidence p3 l ∧ ProjectiveIncidence w l) ∧
      (∃ l ∈ L, ProjectiveIncidence p4 l ∧ ProjectiveIncidence w l)) :
    (W.card : ℝ) - 3 * H ≤ (coordinateGraph T W).card ∧
    (∀ z ∈ coordinateGraph T W, z.1 ≠ 0 ∧ z.2 ≠ 0) ∧
    (((coordinateGraph T W).image Prod.fst).card : ℝ) ≤ H ∧
    (((coordinateGraph T W).image Prod.snd).card : ℝ) ≤ H ∧
    (((coordinateGraph T W).image (fun z => z.1 - z.2)).card : ℝ) ≤ H ∧
    (((coordinateGraph T W).image (fun z => z.1 / z.2)).card : ℝ) ≤ H := by
  have hj1 (z : Point F) (hz : z ∈ coordinateGraph T W) :
      HasJoin (L.image T.lines) (Sum.inr (some 0)) z := by
    simpa only [hT1] using coordinateGraph_hasJoin T W L p1
      (fun w hw => (hjoins w hw).1) z hz
  have hj2 (z : Point F) (hz : z ∈ coordinateGraph T W) :
      HasJoin (L.image T.lines) (Sum.inr none) z := by
    simpa only [hT2] using coordinateGraph_hasJoin T W L p2
      (fun w hw => (hjoins w hw).2.1) z hz
  have hj3 (z : Point F) (hz : z ∈ coordinateGraph T W) :
      HasJoin (L.image T.lines) (Sum.inr (some 1)) z := by
    simpa only [hT3] using coordinateGraph_hasJoin T W L p3
      (fun w hw => (hjoins w hw).2.2.1) z hz
  have hj4 (z : Point F) (hz : z ∈ coordinateGraph T W) :
      HasJoin (L.image T.lines) (Sum.inl (0, 0)) z := by
    simpa only [hT4] using coordinateGraph_hasJoin T W L p4
      (fun w hw => (hjoins w hw).2.2.2) z hz
  have hb := normalized_coordinate_card_bounds (coordinateGraph T W) (L.image T.lines)
    (fun z hz => coordinateGraph_nonzero T W hz)
    (fun z hz => ⟨hj2 z hz, hj1 z hz, hj3 z hz, hj4 z hz⟩)
  have hd1 : ((pencilSlice (L.image T.lines) (Sum.inr (some 0))).card : ℝ) ≤ H := by
    rw [← hT1, card_pencilSlice_image_transform]
    exact hdegree p1 hp1
  have hd2 : ((pencilSlice (L.image T.lines) (Sum.inr none)).card : ℝ) ≤ H := by
    rw [← hT2, card_pencilSlice_image_transform]
    exact hdegree p2 hp2
  have hd3 : ((pencilSlice (L.image T.lines) (Sum.inr (some 1))).card : ℝ) ≤ H := by
    rw [← hT3, card_pencilSlice_image_transform]
    exact hdegree p3 hp3
  have hd4 : ((pencilSlice (L.image T.lines) (Sum.inl (0, 0))).card : ℝ) ≤ H := by
    rw [← hT4, card_pencilSlice_image_transform]
    exact hdegree p4 hp4
  refine ⟨coordinateGraph_card_lower P W T H hWP hcap,
    (fun z hz => coordinateGraph_nonzero T W hz), ?_, ?_, ?_, ?_⟩
  · exact (show (((coordinateGraph T W).image Prod.fst).card : ℝ) ≤
        ((pencilSlice (L.image T.lines) (Sum.inr none)).card : ℝ) by
          exact_mod_cast hb.1).trans hd2
  · exact (show (((coordinateGraph T W).image Prod.snd).card : ℝ) ≤
        ((pencilSlice (L.image T.lines) (Sum.inr (some 0))).card : ℝ) by
          exact_mod_cast hb.2.1).trans hd1
  · exact (show (((coordinateGraph T W).image (fun z => z.1 - z.2)).card : ℝ) ≤
        ((pencilSlice (L.image T.lines) (Sum.inr (some 1))).card : ℝ) by
          exact_mod_cast hb.2.2.1).trans hd3
  · exact (show (((coordinateGraph T W).image (fun z => z.1 / z.2)).card : ℝ) ≤
        ((pencilSlice (L.image T.lines) (Sum.inl (0, 0))).card : ℝ) by
          exact_mod_cast hb.2.2.2).trans hd4

end

end RyserCoveringCounterexample.Incidence

end OAI
