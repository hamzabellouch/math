import OAI.NumberTheory.TotientAsymptotic.NormalitySmallParameter
import OAI.NumberTheory.TotientAsymptotic.NormalityLargeParameter

namespace OAI

/-! Uniform absorption of the finitely many bounded counting endpoints. -/
noncomputable section
namespace TotientAsymptotic

lemma nonnormal_card_le_twice (S : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ((nonNormalPrimes S N).card:ℝ) ≤ 2*N := by
  classical
  have hsub : nonNormalPrimes S N ⊆ Nat.primesLE N := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hc := Finset.card_le_card hsub
  have hp : Nat.primeCounting N ≤ N+1 := Nat.count_le Nat.Prime
  rw [Nat.primesLE_card_eq_primeCounting] at hc
  exact_mod_cast (show (nonNormalPrimes S N).card ≤ 2*N by omega)

lemma normality_bounded_endpoint (M : ℕ) (hM : 4 ≤ M) : ∃ C : ℝ, 0 < C ∧
    ∀ S : ℝ, 2 < S → ∀ N : ℕ, 3 < N → N ≤ M →
    ((nonNormalPrimes S N).card:ℝ) ≤
      C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := by
  classical
  let C := 2*Real.log M*(M:ℝ)^(1/6:ℝ)/(B 4)^5
  have hB4 : 0 < B 4 := by exact doubleLog_nat_pos (n:=4) (by norm_num)
  have hM0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro S hS N hN hNM
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogNM : Real.log N ≤ Real.log M := Real.log_le_log hN0 (by exact_mod_cast hNM)
  have hBN : B 4 ≤ B N := Real.log_le_log (Real.log_pos (by norm_num : (1:ℝ) < 4))
    (Real.log_le_log (by norm_num : (0:ℝ) < 4) (by exact_mod_cast (show 4 ≤ N by omega)))
  have hBpos : 0 < B N := hB4.trans_le hBN
  have hrpow : 0 < (Real.log S)^(-1/6:ℝ) := Real.rpow_pos_of_pos hlogS _
  by_cases hlarge : (N:ℝ) ≤ Real.log S
  · rw [nonNormalPrimes_empty_of_large_parameter hS (by omega) hlarge]
    simp only [Finset.card_empty,Nat.cast_zero]
    dsimp [C]
    positivity
  · have hSM : Real.log S ≤ (M:ℝ) := (le_of_not_ge hlarge).trans (by exact_mod_cast hNM)
    have hr := Real.rpow_le_rpow hlogS.le hSM (by norm_num : (0:ℝ) ≤ 1/6)
    have hpow := pow_le_pow_left₀ hB4.le hBN 5
    have h1 : 1 ≤ Real.log M/Real.log N := (one_le_div hlogN).mpr hlogNM
    have h2 : 1 ≤ (B N)^5/(B 4)^5 := (one_le_div (pow_pos hB4 5)).mpr hpow
    have h3 : 1 ≤ (M:ℝ)^(1/6:ℝ)/(Real.log S)^(1/6:ℝ) :=
      (one_le_div (Real.rpow_pos_of_pos hlogS _)).mpr hr
    have hprod : 1 ≤ (Real.log M/Real.log N)*((B N)^5/(B 4)^5)*
        ((M:ℝ)^(1/6:ℝ)/(Real.log S)^(1/6:ℝ)) := by
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3
    have he : C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) =
        (2*N)*((Real.log M/Real.log N)*((B N)^5/(B 4)^5)*
          ((M:ℝ)^(1/6:ℝ)/(Real.log S)^(1/6:ℝ))) := by
      rw [show (-1/6:ℝ)=-(1/6:ℝ) by norm_num,Real.rpow_neg hlogS.le]
      dsimp [C]
      ring
    rw [he]
    exact (nonnormal_card_le_twice S N (by omega)).trans
      (by have hh := mul_le_mul_of_nonneg_left hprod (show (0:ℝ) ≤ 2*N by positivity); simpa using hh)

end TotientAsymptotic

end

end OAI
