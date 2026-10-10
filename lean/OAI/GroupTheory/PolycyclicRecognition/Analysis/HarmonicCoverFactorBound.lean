import OAI.GroupTheory.PolycyclicRecognition.Analysis.HarmonicCoverEnergy

namespace OAI

/-! # The scale separation needed by the averaging estimate -/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

theorem harmonic_cover_factor_small (S : Finset G) (r R : ℕ) (hR : 0 < R)
    (K : ℝ) (hK : 0 ≤ K)
    (hvol₁ : ((wordBall S (4 * r)).card : ℝ) ≤ K * (wordBall S (2 * r)).card)
    (hvol₂ : ((wordBall S (7 * r)).card : ℝ) ≤ K * (wordBall S r).card)
    (hsep : 32 * (S.card : ℝ) * K ^ 4 * (r : ℝ) ^ 2 < (R : ℝ) ^ 2) :
    harmonicCoverFactor S r R (2 * r) * K ^ 2 < 1 := by
  have hc (n : ℕ) : (0 : ℝ) < (wordBall S n).card :=
    Nat.cast_pos.mpr (card_pos.mpr ⟨1, one_mem_wordBall S n⟩)
  have hratio₁ : ((wordBall S (4 * r)).card : ℝ) / (wordBall S (2 * r)).card ≤ K :=
    (div_le_iff₀ (hc _)).mpr hvol₁
  have hratio₂ : ((wordBall S (7 * r)).card : ℝ) / (wordBall S r).card ≤ K :=
    (div_le_iff₀ (hc _)).mpr hvol₂
  have hprod := mul_le_mul hratio₁ hratio₂ (by positivity) hK
  have hden : 0 < (R : ℝ) + 6 * (r : ℝ) := by exact_mod_cast (by omega : 0 < R + 6 * r)
  have he : harmonicCoverFactor S r R (2 * r) * K ^ 2 =
      (32 * (S.card : ℝ) * (r : ℝ) ^ 2 * K ^ 2 *
        (((wordBall S (4 * r)).card : ℝ) / (wordBall S (2 * r)).card *
          (((wordBall S (7 * r)).card : ℝ) / (wordBall S r).card))) /
        ((R : ℝ) + 6 * (r : ℝ)) ^ 2 := by
    unfold harmonicCoverFactor
    rw [show 2 * (2 * r) = 4 * r by omega, show 3 * (2 * r) + r = 7 * r by omega]
    push_cast
    simp only [one_div, inv_pow]
    ring
  rw [he]
  apply (div_lt_one (sq_pos_of_pos hden)).mpr
  calc
    _ ≤ (32 * (S.card : ℝ) * (r : ℝ) ^ 2 * K ^ 2) * (K * K) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 32 * (S.card : ℝ) * K ^ 4 * (r : ℝ) ^ 2 := by ring
    _ < (R : ℝ) ^ 2 := hsep
    _ ≤ ((R : ℝ) + 6 * (r : ℝ)) ^ 2 := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg R)
      exact le_add_of_nonneg_right (by positivity)

end PolycyclicRecognition

end

end OAI
