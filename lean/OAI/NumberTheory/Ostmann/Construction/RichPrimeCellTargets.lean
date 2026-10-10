import OAI.NumberTheory.Ostmann.Construction.PrimeLogCellMeans

namespace OAI

/-! # Target words in a rich shell of actual primes -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

/-- A shell of positive harmonic mass and positive mean supplies heavy cells
whose ordered indices approximate every sufficiently large target. -/
theorem PublishedProgressionInput.rich_prime_cell_targets
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop, ∀ (P : Finset ℕ) (f : ℕ → ℝ),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, B ≤ primeLogIndex p ∧ (primeLogIndex p : ℝ) ≤ 3 * B) →
      (∀ p ∈ P, f p ≤ 1) → c ≤ ∑ p ∈ P, (p : ℝ)⁻¹ →
      δ * (∑ p ∈ P, (p : ℝ)⁻¹) ≤ ∑ p ∈ P, (p : ℝ)⁻¹ * f p →
      ∀ T : ℝ, C * B ≤ T → ∃ (n : ℕ) (w : List ℕ),
        w.length = n ∧
        (∀ h ∈ w,
          δ * c / (32 * B) ≤ finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h ∧
          δ / 2 ≤ finiteCellMean P primeLogIndex (fun p => (p : ℝ)⁻¹) f h) ∧
        |(w.sum : ℝ) - T| < 64 / (δ * c) ∧
        (n : ℝ) * B ≤ 128 / (δ * c) * T := by
  let ε := δ * c / 64
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C, hC, htargets⟩ := dense_index_target ε hε
  refine ⟨4 * C, by positivity, ?_⟩
  filter_upwards [P0.primeLogIndex_mass_bound,
    eventually_ge_atTop (max (1 : ℝ) (32 / (δ * c)))] with B hmass hB P f hP hlabel hf htotal hbias T hT
  have hB1 : 1 ≤ B := (le_max_left _ _).trans hB
  have hBpos : 0 < B := by linarith
  have hδc : 0 < δ * c := mul_pos hδ hc
  have hlarge : 32 ≤ δ * c * B := by
    have hh := (le_max_right (1 : ℝ) (32 / (δ * c))).trans hB
    exact (div_le_iff₀ hδc).mp hh |>.trans_eq (by ring)
  let I := P.image primeLogIndex
  let N := ⌊3 * B⌋₊
  let μ : ℕ → ℝ := fun p => (p : ℝ)⁻¹
  let θ := δ * c / (32 * B)
  let w := finiteCellMass P primeLogIndex μ
  let score := finiteCellMean P primeLogIndex μ f
  let G := positiveHeavyCells I w score δ θ
  have hIlabel : ∀ p ∈ P, primeLogIndex p ∈ I := fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hIbound : ∀ h ∈ I, h ≤ N := by
    intro h hh
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
    exact Nat.le_floor (hlabel p hp).2
  have hN : (N : ℝ) ≤ 3 * B := Nat.floor_le (by positivity)
  have hBN : B ≤ (N : ℝ) := by
    have hh := Nat.lt_floor_add_one (3 * B)
    change 3 * B < (N : ℝ) + 1 at hh
    linarith
  have hIcard : (I.card : ℝ) ≤ 4 * B := by
    have hh : I.card ≤ N + 1 := by
      simpa only [Finset.card_range] using Finset.card_le_card
        (show I ⊆ Finset.range (N + 1) from fun h hh => Finset.mem_range.mpr (Nat.lt_succ_of_le (hIbound h hh)))
    have hhr : (I.card : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hh
    linarith
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hthin : I.card * θ ≤ (δ / 4) * ∑ p ∈ P, μ p := by
    have hh := mul_le_mul_of_nonneg_right hIcard hθ
    have heq : (4 * B) * θ = δ * c / 8 := by dsimp [θ]; field_simp; ring
    rw [heq] at hh
    have htot := mul_le_mul_of_nonneg_left htotal hδ.le
    dsimp [μ]
    linarith
  have hcap : ∀ h ∈ I, w h ≤ 2 / B := by
    intro h hh
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hh
    exact hmass P hP h (heq ▸ (hlabel p hp).1)
  have hgrowth : (δ / 4) * (∑ p ∈ P, μ p) ≤ G.card * (2 / B) :=
    finite_positive_heavy_cells P I primeLogIndex μ f hIlabel
      (fun p _ => by positivity) hf δ θ (2 / B) hδ.le hθ hbias hthin hcap
  have hGcard : δ * c * B / 8 ≤ G.card := by
    have hh := mul_le_mul_of_nonneg_right hgrowth hBpos.le
    have hcW := mul_le_mul_of_nonneg_left htotal (mul_nonneg hδ.le hBpos.le)
    have heq : (G.card * (2 / B)) * B = 2 * G.card := by field_simp
    rw [heq] at hh
    dsimp [μ] at hh
    nlinarith
  have hGdensity : ε * N + 2 ≤ G.card := by
    have hh := mul_le_mul_of_nonneg_left hN hε.le
    dsimp [ε] at hh ⊢
    nlinarith
  have hGbound : ∀ h ∈ G, h ≤ N := fun h hh => hIbound h (Finset.mem_filter.mp hh).1
  have hCT : C * N ≤ T :=
    (mul_le_mul_of_nonneg_left hN hC.le).trans (by nlinarith)
  obtain ⟨n, u, hlen, hmem, herr, hn, _⟩ := htargets G N hGbound hGdensity T hCT
  refine ⟨n, u, hlen, ?_, ?_, ?_⟩
  · intro h hh
    have hh' := (Finset.mem_filter.mp (hmem h hh)).2
    exact ⟨hh'.2, hh'.1⟩
  · have heq : ε⁻¹ = 64 / (δ * c) := by dsimp [ε]; field_simp
    rwa [heq] at herr
  · have hh := (mul_le_mul_of_nonneg_left hBN (Nat.cast_nonneg (α := ℝ) n)).trans hn
    have heq : 2 * T / ε = 128 / (δ * c) * T := by dsimp [ε]; field_simp; ring
    rwa [heq] at hh

end Ostmann

end OAI
