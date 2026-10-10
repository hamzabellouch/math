import OAI.Combinatorics.Ryser.Geometry.ProjectiveJoins
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section
variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

def HasJoin (L : Finset (ProjectiveLine F)) (p : ProjectivePoint F) (z : Point F) : Prop :=
  ∃ l ∈ L, ProjectiveIncidence p l ∧ ProjectiveIncidence (Sum.inl z) l

def pencilSlice (L : Finset (ProjectiveLine F)) (p : ProjectivePoint F) :
    Finset (ProjectiveLine F) :=
  L.filter fun l => ProjectiveIncidence p l

private theorem line_mem_of_hasJoin {L : Finset (ProjectiveLine F)}
    {p : ProjectivePoint F} {z : Point F} {l : ProjectiveLine F}
    (hne : p ≠ Sum.inl z) (h : HasJoin L p z)
    (hp : ProjectiveIncidence p l) (hz : ProjectiveIncidence (Sum.inl z) l) :
    l ∈ L := let _ := instDecidableEqF; by
  obtain ⟨m, hm, hpm, hzm⟩ := h
  have heq : l = m := eq_projectiveLine_of_common_incidence hne hp hz hpm hzm
  rw [heq]
  exact hm

theorem normalized_witness_lines {L : Finset (ProjectiveLine F)} {z : Point F}
    (hz : z.1 ≠ 0)
    (hV : HasJoin L (Sum.inr none) z)
    (hH : HasJoin L (Sum.inr (some 0)) z)
    (hD : HasJoin L (Sum.inr (some 1)) z)
    (hO : HasJoin L (Sum.inl (0, 0)) z) :
    some (none, z.1) ∈ L ∧ some (some 0, z.2) ∈ L ∧
      some (some 1, -(z.1 - z.2)) ∈ L ∧
      some (some (z.1 / z.2)⁻¹, 0) ∈ L := by
  have hfinite (d : Direction F) : Sum.inr d ≠ (Sum.inl z : ProjectivePoint F) := by
    intro h
    cases h
  have horigin : (Sum.inl (0, 0) : ProjectivePoint F) ≠ Sum.inl z := by
    intro h
    exact hz (congrArg Prod.fst (Sum.inl.inj h)).symm
  refine ⟨line_mem_of_hasJoin (hfinite none) hV rfl rfl, ?_, ?_, ?_⟩
  · apply line_mem_of_hasJoin (l := some (some 0, z.2)) (hfinite (some 0)) hH rfl
    simp only [ProjectiveIncidence, Incidence, projection, zero_mul, sub_zero]
  · apply line_mem_of_hasJoin (l := some (some 1, -(z.1 - z.2))) (hfinite (some 1)) hD rfl
    simp only [ProjectiveIncidence, Incidence, projection, one_mul, neg_sub]
  · apply line_mem_of_hasJoin horigin hO
    · simp only [ProjectiveIncidence, Incidence, projection, mul_zero, sub_self]
    · change z.2 - (z.1 / z.2)⁻¹ * z.1 = 0
      rw [inv_div, div_mul_cancel₀ _ hz, sub_self]

private theorem card_image_le_pencilSlice
    (G : Finset (Point F)) (L : Finset (ProjectiveLine F))
    (p : ProjectivePoint F) (f : Point F → F) (ell : F → ProjectiveLine F)
    (hinj : Function.Injective ell)
    (hline : ∀ z ∈ G, ell (f z) ∈ L)
    (hp : ∀ a, ProjectiveIncidence p (ell a)) :
    (G.image f).card ≤ (pencilSlice L p).card := by
  apply Finset.card_le_card_of_injOn ell
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_filter.mpr ⟨hline z hz, hp (f z)⟩
  · exact fun _ _ _ _ h => hinj h

theorem normalized_coordinate_card_bounds
    (G : Finset (Point F)) (L : Finset (ProjectiveLine F))
    (hnonzero : ∀ z ∈ G, z.1 ≠ 0 ∧ z.2 ≠ 0)
    (hjoins : ∀ z ∈ G,
      HasJoin L (Sum.inr none) z ∧ HasJoin L (Sum.inr (some 0)) z ∧
      HasJoin L (Sum.inr (some 1)) z ∧ HasJoin L (Sum.inl (0, 0)) z) :
    (G.image Prod.fst).card ≤ (pencilSlice L (Sum.inr none)).card ∧
    (G.image Prod.snd).card ≤ (pencilSlice L (Sum.inr (some 0))).card ∧
    (G.image (fun z => z.1 - z.2)).card ≤
      (pencilSlice L (Sum.inr (some 1))).card ∧
    (G.image (fun z => z.1 / z.2)).card ≤
      (pencilSlice L (Sum.inl (0, 0))).card := by
  have hlines (z : Point F) (hz : z ∈ G) := normalized_witness_lines
    (hnonzero z hz).1 (hjoins z hz).1 (hjoins z hz).2.1
      (hjoins z hz).2.2.1 (hjoins z hz).2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply card_image_le_pencilSlice G L (Sum.inr none) Prod.fst
      (fun a => some (none, a))
    · intro a b h
      exact congrArg Prod.snd (Option.some.inj h)
    · exact fun z hz => (hlines z hz).1
    · exact fun _ => rfl
  · apply card_image_le_pencilSlice G L (Sum.inr (some 0)) Prod.snd
      (fun a => some (some 0, a))
    · intro a b h
      exact congrArg Prod.snd (Option.some.inj h)
    · exact fun z hz => (hlines z hz).2.1
    · exact fun _ => rfl
  · apply card_image_le_pencilSlice G L (Sum.inr (some 1)) (fun z => z.1 - z.2)
      (fun a => some (some 1, -a))
    · intro a b h
      exact neg_injective (congrArg Prod.snd (Option.some.inj h))
    · exact fun z hz => (hlines z hz).2.2.1
    · exact fun _ => rfl
  · apply card_image_le_pencilSlice G L (Sum.inl (0, 0)) (fun z => z.1 / z.2)
      (fun a => some (some a⁻¹, 0))
    · intro a b h
      exact inv_injective (Option.some.inj (congrArg Prod.fst (Option.some.inj h)))
    · exact fun z hz => (hlines z hz).2.2.2
    · intro a
      simp only [ProjectiveIncidence, Incidence, projection, mul_zero, sub_self]

theorem zero_not_mem_coordinate_images {G : Finset (Point F)}
    (hnonzero : ∀ z ∈ G, z.1 ≠ 0 ∧ z.2 ≠ 0) :
    (0 : F) ∉ G.image Prod.fst ∧ (0 : F) ∉ G.image Prod.snd := by
  constructor
  · intro h
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp h
    exact (hnonzero z hz).1 heq
  · intro h
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp h
    exact (hnonzero z hz).2 heq

end
end RyserCoveringCounterexample.Incidence

end OAI
