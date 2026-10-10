import OAI.NumberTheory.CubicMoment.Estimates.SmallBHeightBlocks
import OAI.NumberTheory.CubicMoment.Estimates.CoreIndexLogCount
import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicWeightFamily

namespace OAI

/-! Explicit absolute exponents for the arbitrary-coefficient height
bound. The small core is cut at 5832*N^(1/1000). -/
noncomputable section
namespace CubicFirstMoment

lemma smallB_log_square_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N →
    (1+Real.log N)^2 ≤ C*N^(1/40000:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := log_power_normalization_bound 2
    (by norm_num : (0:ℝ) < 1/40000)
  refine ⟨C,hC,?_⟩
  intro N hN
  have hp : 0 < N := zero_lt_one.trans_le hN
  have h := mul_le_mul_of_nonneg_left (hbound N hN) (Real.rpow_nonneg hp.le (1/40000:ℝ))
  rw [← mul_assoc,← Real.rpow_add hp] at h
  norm_num at h
  simpa only [mul_comm C] using h

lemma smallB_height_bracket_power {N T n CI CL : ℝ}
    (hN : 1 ≤ N) (hT : N^(1/50:ℝ) ≤ T) (hCI : 0 ≤ CI) (hCL : 0 ≤ CL)
    (hn : n ≤ CI*(1+Real.log N)^2)
    (hlog : (1+Real.log N)^2 ≤ CL*N^(1/40000:ℝ)) :
    N^(1/10000:ℝ)*(5832*N^(1/1000:ℝ))*(1+N/T)+
      n*N^(2*(1/10000):ℝ)*
        (N/((5832*N^(1/1000:ℝ))/5832)^(1/3:ℝ)+N^(23/24:ℝ)) ≤
      (11664+2*CI*CL)*N^(1-1/20000:ℝ) := by
  have hp : 0 < N := zero_lt_one.trans_le hN
  have hTp : 0 < T := (Real.rpow_pos_of_pos hp _).trans_le hT
  have hfrac : N/T ≤ N^(49/50:ℝ) := by
    calc
      _ ≤ N/N^(1/50:ℝ) := div_le_div_of_nonneg_left hp.le (Real.rpow_pos_of_pos hp _) hT
      _ = _ := by nth_rw 1 [← Real.rpow_one N]; rw [← Real.rpow_sub hp]; norm_num
  have hone : 1+N/T ≤ 2*N^(49/50:ℝ) := by
    linarith [Real.one_le_rpow hN (by norm_num : (0:ℝ) ≤ 49/50)]
  have hsmall : N^(1/10000:ℝ)*(5832*N^(1/1000:ℝ))*(1+N/T) ≤
      11664*N^(1-1/20000:ℝ) := by
    calc
      _ ≤ N^(1/10000:ℝ)*(5832*N^(1/1000:ℝ))*(2*N^(49/50:ℝ)) :=
        mul_le_mul_of_nonneg_left hone (by positivity)
      _ = 11664*N^((1/10000:ℝ)+1/1000+49/50) := by
        repeat rw [Real.rpow_add hp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN (by norm_num)) (by norm_num)
  have hroot : ((5832*N^(1/1000:ℝ))/5832)^(1/3:ℝ) = N^(1/3000:ℝ) := by
    rw [show (5832*N^(1/1000:ℝ))/5832 = N^(1/1000:ℝ) by ring,
      ← Real.rpow_mul hp.le]
    norm_num
  have hdivide : N/N^(1/3000:ℝ) = N^(1-1/3000:ℝ) := by
    nth_rw 1 [← Real.rpow_one N]
    rw [← Real.rpow_sub hp]
  have hn' : n ≤ (CI*CL)*N^(1/40000:ℝ) :=
    hn.trans ((mul_le_mul_of_nonneg_left hlog hCI).trans_eq (by ring))
  have hbig : n*N^(2*(1/10000):ℝ)*
      (N/((5832*N^(1/1000:ℝ))/5832)^(1/3:ℝ)+N^(23/24:ℝ)) ≤
      2*CI*CL*N^(1-1/20000:ℝ) := by
    rw [hroot,hdivide]
    calc
      _ ≤ ((CI*CL)*N^(1/40000:ℝ))*N^(2*(1/10000):ℝ)*
          (N^(1-1/3000:ℝ)+N^(23/24:ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn' (by positivity)) (by positivity)
      _ = (CI*CL)*(N^((1/40000:ℝ)+2*(1/10000)+(1-1/3000))+
          N^((1/40000:ℝ)+2*(1/10000)+23/24)) := by
        repeat rw [Real.rpow_add hp]
        ring
      _ ≤ (CI*CL)*(N^(1-1/20000:ℝ)+N^(1-1/20000:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCI hCL)
        exact add_le_add (Real.rpow_le_rpow_of_exponent_le hN (by norm_num))
          (Real.rpow_le_rpow_of_exponent_le hN (by norm_num))
      _ = _ := by ring
  exact (add_le_add hsmall hbig).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
