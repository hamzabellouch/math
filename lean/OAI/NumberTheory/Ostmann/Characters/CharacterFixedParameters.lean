import OAI.NumberTheory.Ostmann.Characters.CharacterDepthParameters

namespace OAI

/-! # One gap choice and one depth threshold for every selected prime band -/
namespace Ostmann

/-- All rates here precede the finite choice of the three bands and the rich
block depth. The number of cells affects only the later large-L threshold. -/
theorem exists_character_fixed_parameters (a β c δ Ctotal C₀ : ℝ)
    (hβ : 0 < β) (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC₀ : 0 < C₀) (Kmin : ℕ) :
    let Aend := 8 * β + 10
    let Bword := β + 1 - 2 * Real.log δ
    let B₁ := Aend + 2 * Bword + 3
    let Cdy := β + Real.log ((Real.log 2)⁻¹ + 1)
    let Cfinal := β + 1 + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + 1
    0 ≤ Bword ∧ 0 ≤ B₁ ∧ ∃ B : ℝ, 1 ≤ B ∧ 2 * B₁ + 5 ≤ B ∧
      2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
        (Aend + 2 * Bword + 1) + 2) ≤ B ∧
      2 * B₁ + (Cdy / a + max (Real.log 3) 0 + 1) + Real.log 2 + 6 ≤
        B + 20 * Real.log a ∧
      ∃ K : ℕ, Kmin ≤ K ∧ 20000 ≤ K ∧ ∀ k : ℕ, K ≤ k →
        1 < cellRoleScale k ∧ C₀ ≤ Real.exp ((k : ℝ) / 10000) ∧
        Cfinal + (B + 20 * Real.log (cellRoleScale k) + 1) + 2 * B₁ + 1 ≤
          ((k - 1 : ℕ) : ℝ) * Real.log 2 - 1 ∧
        4 * (β + 1) *
          (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) ≤ cellRoleScale k := by
  intro Aend Bword B₁ Cdy Cfinal
  have hlog : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hword : 0 ≤ Bword := by dsimp only [Bword]; linarith only [hβ, hlog]
  have hB₁ : 0 ≤ B₁ := by dsimp only [B₁, Aend]; linarith only [hβ, hword]
  obtain ⟨B, hB, hstrong, hrepeat, hanchor⟩ :=
    character_strong_gap_choice a Ctotal Aend Bword Cdy 1
  obtain ⟨K, hK, hKlarge, hdepth⟩ := character_complete_depth_cutoff
    c δ (β + 1) Cfinal B B₁ C₀ hc hδ (by linarith) hC₀ Kmin
  exact ⟨hword, hB₁, B, hB, hstrong, hrepeat, hanchor, K, hK, hKlarge, hdepth⟩

end Ostmann

end OAI
