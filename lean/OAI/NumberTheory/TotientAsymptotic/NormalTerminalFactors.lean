import OAI.NumberTheory.TotientAsymptotic.NormalBandAllocation
import OAI.NumberTheory.TotientAsymptotic.ResidualFactorCount

namespace OAI

/-! A normal shifted prime contributes few factors below the terminal cutoff. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma partBelow_omega (n : ℕ) (V : ℝ) :
    (partBelow n V).primeFactorsList.length=omegaIn n 1 V := by
  rw [← (partBelow_factors n V).length_eq]
  unfold omegaIn
  congr 1
  apply List.filter_congr
  intro p hp
  have hp1 : (1:ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactorsList hp).one_lt
  simp only [hp1,true_and]

lemma normal_terminal_omega {S V : ℝ} {p : ℕ} (hp : IsNormalPrime S p)
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSV : S ≤ V) :
    ((partBelow (p-1) V).primeFactorsList.length:ℝ) ≤ 4*B V := by
  have hBV : B S ≤ B V := Real.log_le_log (Real.log_pos hS)
    (Real.log_le_log (by linarith) hSV)
  have hB0 : 0 ≤ B V := hBS.trans hBV
  by_cases he : S=V
  · rw [partBelow_omega,← he]
    linarith [hp.2.1]
  · have hlt : S < V := lt_of_le_of_ne hSV he
    have hsplit := congrArg (fun n : ℕ => n.primeFactorsList.length)
      (partBelow_band_split (p-1) hSV)
    rw [omega_count_mul (partBelow_pos (p-1) S).ne' (partBetween_pos (p-1) S V).ne',
      partBelow_omega,partBetween_omega] at hsplit
    have hsR : ((partBelow (p-1) V).primeFactorsList.length:ℝ)=
        (omegaIn (p-1) 1 S:ℝ)+(omegaIn (p-1) S V:ℝ) := by exact_mod_cast hsplit.symm
    have hband := normality_band_upper hp hS hBS le_rfl hlt
    have hroot : Real.sqrt (B S*B V) ≤ B V := Real.sqrt_le_iff.mpr
      ⟨hB0,by nlinarith [mul_le_mul_of_nonneg_right hBV hB0]⟩
    rw [hsR]
    linarith [hp.2.1]

lemma normal_terminal_product_omega {k : ℕ} (p : Fin k → ℕ) {S V : ℝ}
    (hp : ∀ j,IsNormalPrime S (p j)) (hS : 1 < S) (hBS : 0 ≤ B S) (hSV : S ≤ V) :
    ((∏ j,partBelow (p j-1) V).primeFactorsList.length:ℝ) ≤ 4*(k:ℝ)*B V := by
  rw [omega_count_prod _ _ (fun j _ => (partBelow_pos (p j-1) V).ne'),Nat.cast_sum]
  calc
    _ ≤ ∑ _j : Fin k,(4*B V) :=
      Finset.sum_le_sum (fun j _ => normal_terminal_omega (hp j) hS hBS hSV)
    _ = _ := by simp; ring

end TotientAsymptotic

end

end OAI
