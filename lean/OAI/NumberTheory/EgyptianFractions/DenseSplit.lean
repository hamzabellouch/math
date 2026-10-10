import Mathlib

namespace OAI
namespace Problem337

/-- The elementary dense-set step: fewer than half the possible summands
can be missing, so one additive decomposition has both summands present. -/
theorem dense_split_of_complement_card
    (G : Finset ℕ) (N n : ℕ) (hnN : n ≤ N)
    (hcard : 2 * (Finset.Icc 1 N \ G).card < n - 1) :
    ∃ u ∈ G, ∃ w ∈ G, u + w = n := by
  classical
  let H := Finset.Icc 1 N \ G
  by_contra hsplit
  push Not at hsplit
  have hcover : Finset.Icc 1 (n - 1) ⊆ H ∪ H.image (fun w => n - w) := by
    intro u hu
    obtain ⟨hu1, hun⟩ := Finset.mem_Icc.mp hu
    by_cases hgu : u ∈ G
    · have hng : n - u ∉ G := by
        intro hmem
        exact hsplit u hgu (n - u) hmem (by omega)
      have hnH : n - u ∈ H := by
        apply Finset.mem_sdiff.mpr
        exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hng⟩
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨n - u, hnH, by omega⟩
    · apply Finset.mem_union_left
      apply Finset.mem_sdiff.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hu1, by omega⟩, hgu⟩
  have hle := Finset.card_le_card hcover
  have hunion := Finset.card_union_le H (H.image (fun w => n - w))
  have himage := Finset.card_image_le (s := H) (f := fun w => n - w)
  have hinterval : (Finset.Icc 1 (n - 1)).card = n - 1 := by
    simp
  rw [hinterval] at hle
  change 2 * H.card < n - 1 at hcard
  omega

/-- The numerical form used in the manuscript: an exceptional set of size
at most `X / 8` cannot obstruct all splits of an integer in `[X/2, X]`. -/
theorem dense_split_of_real_card
    (G : Finset ℕ) (X : ℝ) (n : ℕ)
    (hX : 4 < X) (hnlo : X / 2 ≤ (n : ℝ)) (hnhi : (n : ℝ) ≤ X)
    (hcard : ((Finset.Icc 1 ⌊X⌋₊ \ G).card : ℝ) ≤ X / 8) :
    ∃ u ∈ G, ∃ w ∈ G, u + w = n := by
  apply dense_split_of_complement_card G ⌊X⌋₊ n (Nat.le_floor hnhi)
  have hn1 : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    subst n
    norm_num at hnlo
    linarith
  have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    simp only [Nat.cast_sub hn1, Nat.cast_one]
  have hreal : (2 : ℝ) * (Finset.Icc 1 ⌊X⌋₊ \ G).card < (n - 1 : ℕ) := by
    rw [hsub]
    linarith
  exact_mod_cast hreal

end Problem337

end OAI
