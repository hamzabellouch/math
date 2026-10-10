import OAI.Combinatorics.Ryser.Construction.GadgetCover

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def GadgetCoverProperty (Y : Finset (Point F)) : Prop :=
  ∀ (B : Finset (Point F)) (L : Finset (AffineLine F)),
    (∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell) →
    2 * L.card + B.card ≤ 2 * Fintype.card F →
    ∃ d : Direction F, L = affinePencil (Sum.inr d) ∧ B = ∅

theorem gadgetCoverProperty_of_near_pencils
    (Y : Finset (Point F))
    (hlarge : 200 < 19 * Fintype.card F)
    (hlines : ∀ ell : AffineLine F,
      Fintype.card F ≤ 8 * (Y ∩ linePoints ell).card)
    (hnear : ∀ (B : Finset (Point F)) (L : Finset (AffineLine F)),
      (∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell) →
      2 * L.card + B.card ≤ 2 * Fintype.card F →
      ∃ p : ProjectivePoint F,
        99 * Fintype.card F ≤ 100 * (L ∩ affinePencil p).card) :
    GadgetCoverProperty Y := by
  intro B L hcover hbudget
  exact mixed_cover_eq_parallel_of_near_pencil Y B L hlarge hlines
    hcover hbudget (hnear B L hcover hbudget)

theorem GadgetCoverProperty.weighted_card_lower_bound
    {Y : Finset (Point F)} (hY : GadgetCoverProperty Y)
    (B : Finset (Point F)) (L : Finset (AffineLine F))
    (hcover : ∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell) :
    2 * Fintype.card F ≤ 2 * L.card + B.card := by
  by_cases hbudget : 2 * L.card + B.card ≤ 2 * Fintype.card F
  · obtain ⟨d, hL, hB⟩ := hY B L hcover hbudget
    have hcard : L.card = Fintype.card F := by
      rw [hL, card_affinePencil_infinite]
    have hBcard : B.card = 0 := by rw [hB, Finset.card_empty]
    omega
  · omega

theorem GadgetCoverProperty.not_line_cover_of_distinct_directions
    {Y : Finset (Point F)} (hY : GadgetCoverProperty Y)
    (L : Finset (AffineLine F)) (hcard : L.card ≤ Fintype.card F)
    {ell m : AffineLine F} (hell : ell ∈ L) (hm : m ∈ L)
    (hdirections : ell.1 ≠ m.1) :
    ¬ (∀ y ∈ Y, ∃ l ∈ L, Incidence y l) := by
  intro hcover
  have hmixed : ∀ y ∈ Y,
      y ∈ (∅ : Finset (Point F)) ∨ ∃ l ∈ L, Incidence y l := by
    intro y hy
    exact Or.inr (hcover y hy)
  have hbudget : 2 * L.card + (∅ : Finset (Point F)).card ≤
      2 * Fintype.card F := by
    simpa only [Finset.card_empty, Nat.add_zero] using Nat.mul_le_mul_left 2 hcard
  obtain ⟨d, hL, _⟩ := hY ∅ L hmixed hbudget
  rw [hL] at hell hm
  have hdell : d = ell.1 := (mem_affinePencil (Sum.inr d) ell).mp hell
  have hdm : d = m.1 := (mem_affinePencil (Sum.inr d) m).mp hm
  exact hdirections (hdell.symm.trans hdm)

theorem mixed_cover_weighted_card_lower_bound_of_near_pencils
    (Y B : Finset (Point F)) (L : Finset (AffineLine F))
    (hlarge : 200 < 19 * Fintype.card F)
    (hlines : ∀ ell : AffineLine F,
      Fintype.card F ≤ 8 * (Y ∩ linePoints ell).card)
    (hnear : ∀ (B : Finset (Point F)) (L : Finset (AffineLine F)),
      (∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell) →
      2 * L.card + B.card ≤ 2 * Fintype.card F →
      ∃ p : ProjectivePoint F,
        99 * Fintype.card F ≤ 100 * (L ∩ affinePencil p).card)
    (hcover : ∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell) :
    2 * Fintype.card F ≤ 2 * L.card + B.card :=
  (gadgetCoverProperty_of_near_pencils Y hlarge hlines hnear).weighted_card_lower_bound
    B L hcover

theorem not_line_cover_of_distinct_directions_of_near_pencils
    (Y : Finset (Point F)) (L : Finset (AffineLine F))
    (hlarge : 200 < 19 * Fintype.card F)
    (hlines : ∀ ell : AffineLine F,
      Fintype.card F ≤ 8 * (Y ∩ linePoints ell).card)
    (hnear : ∀ (B : Finset (Point F)) (L : Finset (AffineLine F)),
      (∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell) →
      2 * L.card + B.card ≤ 2 * Fintype.card F →
      ∃ p : ProjectivePoint F,
        99 * Fintype.card F ≤ 100 * (L ∩ affinePencil p).card)
    (hcard : L.card ≤ Fintype.card F)
    {ell m : AffineLine F} (hell : ell ∈ L) (hm : m ∈ L)
    (hdirections : ell.1 ≠ m.1) :
    ¬ (∀ y ∈ Y, ∃ l ∈ L, Incidence y l) :=
  GadgetCoverProperty.not_line_cover_of_distinct_directions
    (gadgetCoverProperty_of_near_pencils Y hlarge hlines hnear)
    L hcard hell hm hdirections

end RyserCoveringCounterexample.Construction

end OAI
