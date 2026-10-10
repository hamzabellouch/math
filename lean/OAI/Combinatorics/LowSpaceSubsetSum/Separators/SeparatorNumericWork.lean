import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorConcreteIncidence
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorExpectedWork

namespace OAI

/-! # Polynomial factors in the actual separator work estimate -/

noncomputable section

namespace LowSpaceSubsetSum.SeparatorExpectation

open scoped BigOperators

theorem incidence_plus_one_le (g u : ℕ) (hu : 256 ≤ u) (hgu : g + 1 ≤ u)
    {t : ℝ} (ht : t ≤ (11 * 2 ^ 22 : ℝ) * ((g : ℝ) + 1) *
      (2 : ℝ) ^ ((g : ℝ) * (1 - binaryEntropy (1 / 4)))) :
    1 + t ≤ (u : ℝ) ^ 5 * (2 : ℝ) ^ ((g : ℝ) * (1 - binaryEntropy (1 / 4))) := by
  let R := (2 : ℝ) ^ ((g : ℝ) * (1 - binaryEntropy (1 / 4)))
  have hR : 1 ≤ R := Real.one_le_rpow (by norm_num)
    (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (binaryEntropy_le_one _)))
  have hg1 : (1 : ℝ) ≤ (g : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) g]
  have hgR : 1 ≤ ((g : ℝ) + 1) * R := by
    simpa only [one_mul] using mul_le_mul hg1 hR (by norm_num) (by positivity)
  have huR : (256 : ℝ) ≤ u := by exact_mod_cast hu
  have hK : (11 * 2 ^ 22 + 1 : ℝ) ≤ (u : ℝ) ^ 4 := by
    calc
      _ ≤ (256 : ℝ) ^ 4 := by norm_num
      _ ≤ (u : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) huR 4
  have hguR : (g : ℝ) + 1 ≤ u := by exact_mod_cast hgu
  calc
    1 + t ≤ (11 * 2 ^ 22 + 1 : ℝ) * ((g : ℝ) + 1) * R := by
      change t ≤ (11 * 2 ^ 22 : ℝ) * ((g : ℝ) + 1) * R at ht
      nlinarith
    _ ≤ ((u : ℝ) ^ 4 * u) * R := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hK hguR (by positivity) (by positivity)
    _ = _ := by rw [← pow_succ]

theorem incidence_product_le (g u : ℕ) (hu : 256 ≤ u) (hgu : g + 1 ≤ u)
    (t : Fin 4 → ℝ) (ht0 : ∀ i, 0 ≤ t i)
    (ht : ∀ i, t i ≤ (11 * 2 ^ 22 : ℝ) * ((g : ℝ) + 1) *
      (2 : ℝ) ^ ((g : ℝ) * (1 - binaryEntropy (1 / 4)))) :
    (∏ i : Fin 4, (1 + t i)) ≤ (u : ℝ) ^ 20 *
      (2 : ℝ) ^ ((4 * g : ℕ) * (1 - binaryEntropy (1 / 4))) := by
  have hp := Finset.prod_le_prod₀ (s := Finset.univ)
    (fun i _ => show 0 ≤ 1 + t i by linarith [ht0 i])
    (fun i _ => incidence_plus_one_le g u hu hgu (ht i))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
  have hR : ((2 : ℝ) ^ ((g : ℝ) * (1 - binaryEntropy (1 / 4)))) ^ 4 =
      (2 : ℝ) ^ ((4 * g : ℕ) * (1 - binaryEntropy (1 / 4))) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  rwa [mul_pow, ← pow_mul, hR] at hp

theorem separator_coefficient_le (n g u : ℕ) (hu : 256 ≤ u) (hnu : n ≤ u)
    (hgu : g + 1 ≤ u) (ν : Fin 4 → ℕ) (hdepth : ∀ i, Nat.clog 2 (ν i) ≤ g + 4) :
    ((6 * n + 8 + 2 * ∑ i : Fin 4, Nat.clog 2 (ν i) : ℕ) : ℝ) ≤ (u : ℝ) ^ 2 := by
  have hsum : (∑ i : Fin 4, Nat.clog 2 (ν i)) ≤ 4 * (g + 4) := by
    calc
      _ ≤ ∑ _ : Fin 4, (g + 4) := Finset.sum_le_sum (fun i _ => hdepth i)
      _ = _ := by simp
  have hnR : (n : ℝ) ≤ u := by exact_mod_cast hnu
  have hgR : (g : ℝ) + 1 ≤ u := by exact_mod_cast hgu
  have huR : (256 : ℝ) ≤ u := by exact_mod_cast hu
  have hsR : ((∑ i : Fin 4, Nat.clog 2 (ν i) : ℕ) : ℝ) ≤ 4 * ((g : ℝ) + 4) := by
    exact_mod_cast hsum
  push_cast at hsR ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr huR) (Nat.cast_nonneg u)]

end LowSpaceSubsetSum.SeparatorExpectation

end

end OAI
