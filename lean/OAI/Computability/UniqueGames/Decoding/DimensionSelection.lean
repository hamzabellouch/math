import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import OAI.Computability.UniqueGames.Inverse.AffineWitnessLemmas

namespace OAI

section

/-! Logical dimension is chosen after the inverse density and row bound,
and before the tuple length. All row maps, including deficient-rank maps,
satisfy the resulting small trivial-character bound. -/

namespace UniqueGamesTheorem.Decoder.DimensionSelection

noncomputable section

theorem exists_logical_dimension {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (r lower : ℕ) :
    ∃ ell : ℕ, lower ≤ ell ∧ r < ell ∧
      1 / (2 : ℝ) ^ (ell - r) < α / 8 ∧
      1 / (2 : ℝ) ^ ell < η / 4 := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (lt_min (show (0 : ℝ) < α / 8 by positivity)
      (show (0 : ℝ) < η / 4 by positivity))
    (show (1 / 2 : ℝ) < 1 by norm_num)
  let ell := max lower (r + n + 1)
  have hrn : r + n + 1 ≤ ell := le_max_right _ _
  have hr : r < ell := lt_of_lt_of_le (by omega) hrn
  have hnsub : n ≤ ell - r := by omega
  have hnell : n ≤ ell := hnsub.trans (Nat.sub_le _ _)
  have hpow (j : ℕ) (hj : n ≤ j) :
      1 / (2 : ℝ) ^ j < min (α / 8) (η / 4) := by
    have hmon : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
    simpa only [one_div, inv_pow] using hmon.trans_lt hn
  exact ⟨ell, le_max_left _ _, hr,
    (hpow (ell - r) hnsub).trans_le (min_le_left _ _),
    (hpow ell hnell).trans_le (min_le_right _ _)⟩

/-- Uniform choice of `ell` bounds the trivial character fraction for every
possible public row map without conditioning on its rank. -/
theorem kernel_fraction_le {ell r : ℕ}
    (A : (Fin ell → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) [Fintype A.ker] :
    1 / (Fintype.card A.ker : ℝ) ≤ 1 / (2 : ℝ) ^ (ell - r) := by
  have hcard : (2 : ℝ) ^ (ell - r) ≤ (Fintype.card A.ker : ℝ) := by
    have h := Inverse.binary_kernel_card_lower A
    rw [Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  exact one_div_le_one_div_of_le (by positivity) hcard

theorem kernel_fraction_lt {ell r : ℕ} {α : ℝ}
    (A : (Fin ell → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) [Fintype A.ker]
    (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    1 / (Fintype.card A.ker : ℝ) < α / 8 :=
  (kernel_fraction_le A).trans_lt hsmall

end
end UniqueGamesTheorem.Decoder.DimensionSelection

end

end OAI
