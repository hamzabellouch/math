import Mathlib

namespace OAI
namespace Problem337

/-- A dense subset of an initial interval represents an interior integer as a
sum of two of its elements, provided fewer than half its positive splits are
spoiled by missing elements. -/
theorem dense_pairing {N n : ℕ} (G : Finset ℕ) (hn : n ≤ N)
    (hcard : 2 * (Finset.Icc 1 N \ G).card < n - 1) :
    ∃ u ∈ G, ∃ v ∈ G, u + v = n := by
  classical
  by_contra h
  push Not at h
  let H := Finset.Icc 1 N \ G
  have hsub : Finset.Icc 1 (n - 1) ⊆ H ∪ H.image (fun u => n - u) := by
    intro u hu
    have hu' := Finset.mem_Icc.mp hu
    have hun : u ≤ n := by omega
    by_cases huG : u ∈ G
    · have hvG : n - u ∉ G := by
        intro hv
        exact h u huG (n - u) hv (by omega)
      have hvH : n - u ∈ H := by
        apply Finset.mem_sdiff.mpr
        exact ⟨Finset.mem_Icc.mpr (by omega), hvG⟩
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨n - u, hvH, by omega⟩
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr (by omega), huG⟩
  have hc := calc
    (Finset.Icc 1 (n - 1)).card ≤ (H ∪ H.image (fun u => n - u)).card :=
      Finset.card_le_card hsub
    _ ≤ H.card + (H.image (fun u => n - u)).card := Finset.card_union_le _ _
    _ ≤ H.card + H.card := Nat.add_le_add_left Finset.card_image_le _
  have hI : (Finset.Icc 1 (n - 1)).card = n - 1 := by simp
  rw [hI] at hc
  dsimp [H] at hc
  omega

/-- The real-parameter form used in the dense-family argument. -/
theorem dense_pairing_real (X : ℝ) (G : Finset ℕ) (n : ℕ)
    (hX : 4 < X) (hnlow : X / 2 ≤ (n : ℝ)) (hnup : (n : ℝ) ≤ X)
    (hbad : ((Finset.Icc 1 ⌊X⌋₊ \ G).card : ℝ) ≤ X / 8) :
    ∃ u ∈ G, ∃ v ∈ G, u + v = n := by
  apply dense_pairing G (Nat.le_floor hnup)
  have hc : (2 * (Finset.Icc 1 ⌊X⌋₊ \ G).card + 1 : ℝ) < (n : ℝ) := by
    nlinarith
  have hc' : 2 * (Finset.Icc 1 ⌊X⌋₊ \ G).card + 1 < n := by
    exact_mod_cast hc
  omega

/-- The largest integer multiple not exceeding `X` is at least `X / 2`,
provided the step size is positive and does not exceed `X`. -/
theorem floor_multiple_bounds {X a : ℝ} (ha : 0 < a) (haX : a ≤ X) :
    X / 2 ≤ (⌊X / a⌋₊ : ℝ) * a ∧ (⌊X / a⌋₊ : ℝ) * a ≤ X := by
  have ht : 1 ≤ X / a := (le_div_iff₀ ha).mpr (by simpa using haX)
  have hfloor : 1 ≤ ⌊X / a⌋₊ := Nat.le_floor (by simpa using ht)
  have hfloorR : (1 : ℝ) ≤ (⌊X / a⌋₊ : ℝ) := by exact_mod_cast hfloor
  have hlt := Nat.lt_floor_add_one (X / a)
  have hhalf : X / a ≤ 2 * (⌊X / a⌋₊ : ℝ) := by linarith
  have hmul := (div_le_iff₀ ha).mp hhalf
  have hupper := (le_div_iff₀ ha).mp (Nat.floor_le (by positivity : 0 ≤ X / a))
  constructor <;> nlinarith

end Problem337

end OAI
