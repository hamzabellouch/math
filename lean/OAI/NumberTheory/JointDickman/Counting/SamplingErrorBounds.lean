import OAI.NumberTheory.JointDickman.Counting.FiniteSamplingComparison
import OAI.NumberTheory.JointDickman.Amplification.ParameterEstimates

namespace OAI

/-! # Scalar bounds for the manuscript's sampling scales -/

namespace JointDickman
open Filter
open scoped Topology

theorem samplingError_eq {ι : Type*} [Fintype ι] [Nonempty ι]
    (d Q : ℝ) (m : ℕ) :
    samplingError (ι := ι) d Q m =
      2*Real.sqrt (Q/(m : ℝ))+2*m*d/Fintype.card ι := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have he : (Fintype.card ι : ℝ)*((Fintype.card ι : ℝ)/m*Q) =
      (Fintype.card ι : ℝ)^2*(Q/m) := by ring
  unfold samplingError
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hN.le,add_div]
  field_simp

theorem samplingError_scale_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    {B c U K : ℝ} (hB : 1 ≤ B) (hc : 0 < c) (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hNlo : c*B^(0.32 : ℝ) ≤ Fintype.card ι)
    (hNhi : (Fintype.card ι : ℝ) ≤ U*B^(0.32 : ℝ))
    (m : ℕ) (hmlo : B^(0.14 : ℝ) ≤ m) (hmhi : (m : ℝ) ≤ 2*B^(0.14 : ℝ)) :
    samplingError (ι := ι) (K*B^(0.07 : ℝ))
      ((Fintype.card ι : ℝ)*B^(-0.20 : ℝ)) m ≤
      2*Real.sqrt (U*(B^(0.12 : ℝ)/B^(0.14 : ℝ))) +
        (4*K/c)*(B^(0.21 : ℝ)/B^(0.32 : ℝ)) := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hm : (0 : ℝ) < m := (Real.rpow_pos_of_pos hB0 _).trans_le hmlo
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [samplingError_eq]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ (U*B^(0.32 : ℝ)*B^(-0.20 : ℝ))/B^(0.14 : ℝ) := by
        gcongr
      _ = _ := by
        rw [mul_assoc,← Real.rpow_add hB0]
        norm_num
        ring
  · calc
      _ ≤ 2*(2*B^(0.14 : ℝ))*(K*B^(0.07 : ℝ))/(c*B^(0.32 : ℝ)) := by
        gcongr
      _ = _ := by
        have he : B^(0.14 : ℝ)*B^(0.07 : ℝ) = B^(0.21 : ℝ) := by
          rw [← Real.rpow_add hB0]
          norm_num
        field_simp
        nlinarith [he]

theorem sampling_degree_scale_bound {N B C q K U : ℝ}
    (hB : 0 < B) (hC : 0 ≤ C) (hq : 0 ≤ q) (hK : 0 < K) (hN : 0 ≤ N)
    (hNhi : N ≤ U*B^(0.32 : ℝ)) (hgap : 2*C ≤ K*B^(0.07 : ℝ)) :
    N*(q*B^(-0.21 : ℝ))/(K*B^(0.07 : ℝ)-C)^2 ≤
      (4*U*q/K^2)*(B^(0.11 : ℝ)/B^(0.14 : ℝ)) := by
  have hd : 0 < K*B^(0.07 : ℝ) := mul_pos hK (Real.rpow_pos_of_pos hB _)
  have hg : 0 < K*B^(0.07 : ℝ)-C := by linarith
  have hUn : 0 ≤ U*B^(0.32 : ℝ) := hN.trans hNhi
  have hs : (K*B^(0.07 : ℝ))^2/4 ≤ (K*B^(0.07 : ℝ)-C)^2 := by nlinarith
  calc
    _ ≤ (U*B^(0.32 : ℝ))*(q*B^(-0.21 : ℝ))/((K*B^(0.07 : ℝ))^2/4) := by
      gcongr
    _ = _ := by
      have he : B^(0.32 : ℝ)*B^(-0.21 : ℝ) = B^(0.11 : ℝ) := by
        rw [← Real.rpow_add hB]; norm_num
      have he2 : (B^(0.07 : ℝ))^2 = B^(0.14 : ℝ) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hB.le]; norm_num
      rw [mul_pow,he2]
      have hn : (U*B^(0.32 : ℝ))*(q*B^(-0.21 : ℝ)) = U*q*B^(0.11 : ℝ) := by
        calc
          _ = U*q*(B^(0.32 : ℝ)*B^(-0.21 : ℝ)) := by ring
          _ = _ := by rw [he]
      rw [hn]
      field_simp

theorem sampling_square_scale_eq {N B q : ℝ} (hN : N ≠ 0) (hB : 0 < B) :
    N*(q*B^(-0.21 : ℝ))/(N*B^(-0.20 : ℝ)) =
      q*(B^(0.20 : ℝ)/B^(0.21 : ℝ)) := by
  rw [Real.rpow_neg hB.le,Real.rpow_neg hB.le]
  field_simp

theorem sampling_error_envelope_tendsto (U K c : ℝ) :
    Tendsto (fun B : ℝ => 2*Real.sqrt (U*(B^(0.12 : ℝ)/B^(0.14 : ℝ)))+
      (4*K/c)*(B^(0.21 : ℝ)/B^(0.32 : ℝ))) atTop (𝓝 0) := by
  have h₁ := ((power_div_power_tendsto_zero (a := (0.12 : ℝ)) (b := (0.14 : ℝ))
    (by norm_num)).const_mul U).sqrt.const_mul 2
  have h₂ := (power_div_power_tendsto_zero (a := (0.21 : ℝ)) (b := (0.32 : ℝ))
    (by norm_num)).const_mul (4*K/c)
  simpa using h₁.add h₂

end JointDickman

end OAI
