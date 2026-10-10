import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapBilinear

namespace OAI

noncomputable section
namespace Ostmann.Characters
open scoped BigOperators SchwartzMap
attribute [local instance] Classical.propDecidable

def longProgressionMajorant (E b₀ : ℝ) (Q a n : ℕ) : ℝ :=
  let t : ℝ := ((Q*n+a : ℕ) : ℝ)
  if b₀ ≤ t ∧ t ≤ 2*b₀ then E/t else 0

theorem longProgressionMajorant_nonneg {E b₀ : ℝ} (hE : 0 ≤ E) (hb : 0 < b₀)
    (Q a n : ℕ) : 0 ≤ longProgressionMajorant E b₀ Q a n := by
  dsimp only [longProgressionMajorant]
  split_ifs with h
  · exact div_nonneg hE (hb.le.trans h.1)
  · exact le_refl _

theorem longProgressionMajorant_le {E b₀ : ℝ} (hE : 0 ≤ E) (hb : 0 < b₀)
    (Q a n : ℕ) : longProgressionMajorant E b₀ Q a n ≤ E/b₀ := by
  dsimp only [longProgressionMajorant]
  split_ifs with h
  · exact div_le_div_of_nonneg_left hE hb h.1
  · exact div_nonneg hE hb.le

theorem longProgressionMajorant_normalization {E b₀ : ℝ} (hb : 0 < b₀)
    (Q a n : ℕ) :
    (longProgressionMajorant E b₀ Q a n : ℂ) =
      (E/b₀ : ℂ) *
        (if b₀ ≤ ((Q*n+a : ℕ) : ℝ) ∧ ((Q*n+a : ℕ) : ℝ) ≤ 2*b₀
         then historyRatioProfile (Real.log (b₀/((Q*n+a : ℕ) : ℝ))) else 0) := by
  dsimp only [longProgressionMajorant]
  split_ifs with h
  · have ht : 0 < ((Q*n+a : ℕ) : ℝ) := hb.trans_le h.1
    rw [historyRatioProfile,Real.exp_log (div_pos hb ht)]
    push_cast
    have hbC : (b₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
    field_simp
  · simp

theorem longReciprocal_log_range {b₀ t : ℝ} (hb : 0 < b₀)
    (ht : b₀ ≤ t ∧ t ≤ 2*b₀) : Real.log (b₀/t) ∈ Set.Icc (-Real.log 2) 0 := by
  have ht0 : 0 < t := hb.trans_le ht.1
  have hlo : (1/2 : ℝ) ≤ b₀/t := (le_div_iff₀ ht0).mpr (by linarith [ht.2])
  have hhi : b₀/t ≤ 1 := (div_le_one ht0).mpr ht.1
  constructor
  · have h := Real.log_le_log (by norm_num : (0 : ℝ)<1/2) hlo
    simpa only [one_div,Real.log_inv] using h
  · simpa using Real.log_le_log (div_pos hb ht0) hhi

theorem longProgressionMajorant_energy_le {η κ : Type*} [Fintype η] [Fintype κ]
    (Q N : ℕ) (a : η → ℕ) (ν : κ → ℝ) (W : η → ℕ → κ → ℂ)
    {E b₀ A : ℝ} (hE : 0 ≤ E) (hb : 0 < b₀) (_hA : 0 ≤ A)
    (hN : (N : ℝ) ≤ 3*b₀) (hν : ∀ j, 0 ≤ ν j) (hmass : ∑ j, ν j ≤ 1)
    (hW : ∀ r n j, ‖W r n j‖ ≤ A) :
    oneSidedWeightEnergy N (fun r => longProgressionMajorant E b₀ Q (a r)) ν W ≤
      3*(Fintype.card η : ℝ)*E*A^2 := by
  have hA2 : 0 ≤ A^2 := sq_nonneg _
  have hpoint (j : κ) (x : η × Fin N) :
      longProgressionMajorant E b₀ Q (a x.1) x.2 * ‖W x.1 x.2 j‖^2 ≤ (E/b₀)*A^2 :=
    mul_le_mul (longProgressionMajorant_le hE hb _ _ _)
      (pow_le_pow_left₀ (norm_nonneg _) (hW _ _ _) 2) (sq_nonneg _) (div_nonneg hE hb.le)
  have hsum (j : κ) : (∑ x : η × Fin N,
      longProgressionMajorant E b₀ Q (a x.1) x.2 * ‖W x.1 x.2 j‖^2) ≤
      3*(Fintype.card η : ℝ)*E*A^2 := by
    calc
      _ ≤ ∑ _x : η × Fin N, (E/b₀)*A^2 := Finset.sum_le_sum (fun x _ => hpoint j x)
      _ = (Fintype.card η : ℝ)*(N:ℝ)*(E/b₀)*A^2 := by simp [Fintype.card_prod]; ring
      _ ≤ (Fintype.card η : ℝ)*(3*b₀)*(E/b₀)*A^2 := by gcongr
      _ = _ := by field_simp
  unfold oneSidedWeightEnergy
  calc
    _ ≤ ∑ j, ν j*(3*(Fintype.card η : ℝ)*E*A^2) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hsum j) (hν j))
    _ = (∑ j, ν j)*(3*(Fintype.card η : ℝ)*E*A^2) := (Finset.sum_mul ..).symm
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hmass (by positivity : 0 ≤ 3*(Fintype.card η : ℝ)*E*A^2)

end Ostmann.Characters

end

end OAI
