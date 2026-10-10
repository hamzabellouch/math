import OAI.NumberTheory.Ostmann.Characters.MellinParseval

namespace OAI

/-!
# Summing the square-pullback majorants

Every character contributes to exactly one square fiber, and a single
fiber contains at most two characters. These are the two bounds needed
for the same-pair quartet majorant.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance squareMassFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance squareMassDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

noncomputable def squareCharacterMass {p : ℕ} [Fact p.Prime]
    (a : MulChar (ZMod p) ℂ → ℝ) (ρ : MulChar (ZMod p) ℂ) : ℝ :=
  ∑ χ ∈ Finset.univ.filter (fun χ => χ ^ 2 = ρ), a χ

theorem squareCharacterMass_nonneg {p : ℕ} [Fact p.Prime]
    (a : MulChar (ZMod p) ℂ → ℝ) (ha : ∀ χ, 0 ≤ a χ) (ρ : MulChar (ZMod p) ℂ) :
    0 ≤ squareCharacterMass a ρ := Finset.sum_nonneg fun χ _ => ha χ

theorem squareCharacterMass_le_twice {p : ℕ} [Fact p.Prime]
    (a : MulChar (ZMod p) ℂ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ χ, a χ ≤ M) (ρ : MulChar (ZMod p) ℂ) :
    squareCharacterMass a ρ ≤ 2 * M := by
  unfold squareCharacterMass
  calc
    _ ≤ ∑ _χ ∈ Finset.univ.filter (fun χ : MulChar (ZMod p) ℂ => χ ^ 2 = ρ), M :=
      Finset.sum_le_sum fun χ _ => ha χ
    _ = ((Finset.univ.filter (fun χ : MulChar (ZMod p) ℂ => χ ^ 2 = ρ)).card : ℝ) * M := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast mulChar_square_fiber_card_le_two Finset.univ ρ) hM

theorem sum_squareCharacterMass {p : ℕ} [Fact p.Prime]
    (a : MulChar (ZMod p) ℂ → ℝ) :
    (∑ ρ : MulChar (ZMod p) ℂ, squareCharacterMass a ρ) =
      ∑ χ : MulChar (ZMod p) ℂ, a χ := by
  exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) a

end Ostmann

end OAI
