import OAI.NumberTheory.Ostmann.Preliminaries.ResidueSupports

namespace OAI

namespace Ostmann.SiftedWeights
open Finset

def forbiddenResidues (s : Finset ℕ) (p : ℕ) : Finset (ZMod p) :=
  s.image (fun b : ℕ => -(b : ZMod p))

noncomputable def allowedResidues (s : Finset ℕ) (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  (forbiddenResidues s p)ᶜ

theorem forbiddenResidues_card (s : Finset ℕ) {p : ℕ}
    (hp : ∀ b ∈ s, b < p) : (forbiddenResidues s p).card = s.card := by
  classical
  apply Finset.card_image_iff.mpr
  intro a ha b hb heq
  have hcast : (a : ZMod p) = (b : ZMod p) := neg_injective heq
  have hm := (ZMod.natCast_eq_natCast_iff' a b p).mp hcast
  simpa only [Nat.mod_eq_of_lt (hp a ha), Nat.mod_eq_of_lt (hp b hb)] using hm

theorem allowedResidues_card (s : Finset ℕ) {p : ℕ} [NeZero p]
    (hp : ∀ b ∈ s, b < p) : (allowedResidues s p).card = p-s.card := by
  classical
  rw [allowedResidues, Finset.card_compl, ZMod.card p, forbiddenResidues_card s hp]

theorem allowedResidues_nonempty (s : Finset ℕ) {p : ℕ} [NeZero p]
    (hp : ∀ b ∈ s, b < p) (hcard : s.card < p) : (allowedResidues s p).Nonempty := by
  rw [← Finset.card_pos, allowedResidues_card s hp]
  omega

theorem allowedResidues_card_lt (s : Finset ℕ) {p : ℕ} [NeZero p]
    (hp : ∀ b ∈ s, b < p) (hs : s.Nonempty) : (allowedResidues s p).card < p := by
  rw [allowedResidues_card s hp]
  have := Finset.card_pos.mpr hs
  have := NeZero.pos p
  omega

theorem allowedResidues_factor (s : Finset ℕ) {p : ℕ} [NeZero p]
    (hp : ∀ b ∈ s, b < p) (hcard : s.card < p) :
    (p : ℝ)/(allowedResidues s p).card - 1 = (s.card : ℝ)/((p : ℝ)-s.card) := by
  rw [allowedResidues_card s hp, Nat.cast_sub hcard.le]
  have hpos : 0 < (p : ℝ)-s.card := sub_pos.mpr (by exact_mod_cast hcard)
  field_simp
  ring

theorem actual_mem_allowedResidues (d : Ostmann.Decomposition) (s : Finset ℕ)
    (hs : ∀ b ∈ s, b ∈ d.B) {p a : ℕ} [NeZero p] (hp : p.Prime)
    (ha : a ∈ d.A) (hlarge : p+d.cutoff < a) :
    (a : ZMod p) ∈ allowedResidues s p := by
  classical
  apply Finset.mem_compl.mpr
  intro hmem
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hmem
  exact d.residue_ne_neg hp ha (hs b hb) hlarge hba.symm

theorem exists_shift_data (d : Ostmann.Decomposition) (j : ℕ) :
    ∃ s : Finset ℕ, ∃ K : ℕ, s.card = j ∧ j ≤ K ∧
      (∀ b ∈ s, b ∈ d.B) ∧ (∀ p : ℕ, K < p → ∀ b ∈ s, b < p) := by
  obtain ⟨s, hs, hcard⟩ := d.infinite_B.exists_subset_card_eq j
  refine ⟨s, max j (s.sup id), hcard, le_max_left _ _, hs, ?_⟩
  intro p hp b hb
  exact (Finset.le_sup (f := id) hb).trans_lt ((le_max_right _ _).trans_lt hp)

end Ostmann.SiftedWeights

end OAI
