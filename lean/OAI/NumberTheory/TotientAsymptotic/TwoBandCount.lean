import OAI.NumberTheory.TotientAsymptotic.FordNormalCount

namespace OAI

/-! The two-coordinate upper estimate needed to start Ford's counting bootstrap. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def twoBandCutoffs (S z w : ℕ) (j : ℕ) : ℕ := if j=0 then z else if j=1 then w else S

lemma two_band_exponent_le {S z w : ℕ} (hS : 2 ≤ S) (hSw : S ≤ w) (hwz : w ≤ z)
    (hBS : 0 ≤ B S) (D : ℝ) :
    -(∑ j ∈ Finset.range 2,a (j+1)*B (twoBandCutoffs S z w j))+
      (1-countBandWeight 3)*B S+normalBandError S D 2 (twoBandCutoffs S z w) ≤
      -a 1*B z-a 2*B w+4*B S+5*D+8*Real.sqrt (B S*B z) := by
  have hw1 : (1:ℝ) < w := by exact_mod_cast (show 1 < w by omega)
  have hz1 : (1:ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hB : B w ≤ B z := Real.log_le_log (Real.log_pos hw1)
    (Real.log_le_log (by linarith) (by exact_mod_cast hwz))
  have hroot : Real.sqrt (B S*B w) ≤ Real.sqrt (B S*B z) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hB hBS)
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have hlog3 : Real.log (3:ℝ) ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    norm_num at hh
    exact hh
  have hlog3non : 0 ≤ Real.log (3:ℝ) := Real.log_nonneg (by norm_num)
  have hterm := mul_le_mul_of_nonneg_right hlog3 hBS
  have h2 := mul_le_mul_of_nonneg_right hlog2 (Real.sqrt_nonneg (B S*B z))
  have h3 := mul_le_mul_of_nonneg_right hlog3 (Real.sqrt_nonneg (B S*B z))
  have hm := mul_le_mul_of_nonneg_left hroot hlog3non
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,normalBandError,
    twoBandCutoffs,countBandWeight] at *
  norm_num at *
  nlinarith only [hterm,h2,h3,hm]

theorem ford_two_band_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ S X z w : ℕ,2 ≤ S → S ≤ w → w ≤ z → 0 ≤ B S → 1 ≤ B X →
    Real.log z ≤ Real.log X/(20*B X) → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ v ≤ X ∧
      (v.primeFactorsList.length:ℝ) ≤ 5*B X ∧ SquarefreeAbove v S ∧ SquarefreeAbove n S ∧
      (∀ p ∈ n.primeFactors,IsNormalPrime S p) ∧
      3 ≤ n.primeFactorsList.length ∧ z < fordPrime n 1 ∧ w < fordPrime n 2) →
    (Q.card:ℝ) ≤ C*X*Real.exp (-a 1*B z-a 2*B w+4*B S+5*D+8*Real.sqrt (B S*B z)) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := ford_normal_value_count
  refine ⟨C,D,hC,hD,?_⟩
  intro S X z w hS hSw hwz hBS hBX hcut Q hQ
  have hY : ∀ j < 2,twoBandCutoffs S z w (j+1) ≤ twoBandCutoffs S z w j := by
    intro j hj
    interval_cases j
    · simpa [twoBandCutoffs] using hwz
    · simpa [twoBandCutoffs] using hSw
  have hb := hbound S X z 2 (twoBandCutoffs S z w) hS (hSw.trans hwz)
    (by simp [twoBandCutoffs]) (by simp [twoBandCutoffs]) hBX hcut hY Q (by
      intro v hv
      obtain ⟨n,hn,hφ,hvX,hΩ,hsqv,hsqn,hnorm,hlen,hp1,hp2⟩ := hQ v hv
      refine ⟨n,hn,hφ,hvX,hΩ,hsqv,hsqn,hnorm,?_⟩
      intro j
      fin_cases j <;> norm_num [twoBandCutoffs] <;> omega)
  have he := Real.exp_le_exp.mpr (two_band_exponent_le hS hSw hwz hBS D)
  exact hb.trans (mul_le_mul_of_nonneg_left he (by positivity))

end TotientAsymptotic

end

end OAI
