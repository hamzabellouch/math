import OAI.Analysis.FreeEntropy.GUEGradient

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
namespace FiniteEntropySeparation
 theorem gueMatrix_norm_tail_uniform {n d : ℕ} (hd : 0 < d) (i : Fin n) {L : ℝ} (hL : 0 ≤ L) :
    (productGaussian (MatrixIndex n d)).real {x | L < matrixOpNorm (gueMatrix x i)} ≤
      (4*Real.exp 64)*Real.exp (-L^2/64) := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  by_cases hlarge : 64 ≤ L
  · have hlog : 4*Real.log 9 ≤ L^2/64 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<9)
      nlinarith [sq_nonneg (L-64)]
    have he : (4*(d:ℝ))*Real.log 9 - (d:ℝ)*L^2/32 ≤ -L^2/64 := by
      calc
        _ = (d:ℝ)*(4*Real.log 9-L^2/32) := by ring
        _ ≤ (d:ℝ)*(-L^2/64) := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
        _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (sq_nonneg L)]
    calc
      _ ≤ 4*9^(4*d)*Real.exp (-((d:ℝ)*L^2)/32) := gueMatrix_norm_tail hd i hL
      _ = 4*Real.exp ((4*(d:ℝ))*Real.log 9 - (d:ℝ)*L^2/32) := by
        rw [show (9:ℝ)^(4*d)=Real.exp ((4*(d:ℝ))*Real.log 9) by rw [show 4*(d:ℝ)=((4*d:ℕ):ℝ) by push_cast; rfl, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<9)]]
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ 4*Real.exp (-L^2/64) := by gcongr
      _ ≤ _ := by
        have hh : 1 ≤ Real.exp (64:ℝ) := by simp
        nlinarith [Real.exp_pos (-L^2/64)]
  · have hL2 : L^2/64 ≤ 64 := by nlinarith
    have hh : 1 ≤ Real.exp 64*Real.exp (-L^2/64) := by
      rw [← Real.exp_add]; simpa using Real.exp_le_exp.mpr (show 0 ≤ 64 + -L^2/64 by linarith)
    exact (measureReal_le_one).trans (by nlinarith)
 theorem gueMatrix_norm_measurable {n d : ℕ} (i : Fin n) :
    Measurable (fun x : MatrixIndex n d → ℝ => matrixOpNorm (gueMatrix x i)) := by
  unfold gueMatrix
  apply (matrixOpNorm_continuous.comp ?_).measurable
  exact (continuous_const (y := (Real.sqrt d:ℂ)⁻¹)).smul (show Continuous (fun x : MatrixIndex n d → ℝ => coordinateMatrix x i) from
    continuous_pi (fun j => continuous_pi (fun k => (coordinateMatrix_polynomial i j k).continuous)))
 def gaussianMomentMajorant (m : ℕ) : ℝ :=
    (4*Real.exp 64)*(m+1)*∫ t : ℝ in Ioi 0, t^m*Real.exp (-t^2/64)
 theorem gaussianMomentMajorant_nonneg (m : ℕ) : 0 ≤ gaussianMomentMajorant m := by
  apply mul_nonneg (by positivity)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  positivity
 theorem tail_power_integral {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z) (hZ0 : ∀ x, 0 ≤ Z x)
    (htail : ∀ t ≥ 0, μ.real {x | t < Z x} ≤ (4*Real.exp 64)*Real.exp (-t^2/64)) (m : ℕ) :
    Integrable (fun x => Z x^(m+1)) μ ∧ (∫ x, Z x^(m+1) ∂μ) ≤ gaussianMomentMajorant m := by
  have hi : IntegrableOn (fun t : ℝ => t^m*Real.exp (-t^2/64)) (Ioi 0) := by
    convert integrableOn_rpow_mul_exp_neg_mul_sq (b := (1:ℝ)/64) (by norm_num) (s := (m:ℝ)) (by have := Nat.cast_nonneg (α := ℝ) m; linarith) using 1
    simp only [Real.rpow_natCast]
    funext t
    congr 1
    congr 1
    ring
  have hi' := hi.const_mul ((4*Real.exp 64)*(m+1))
  have hpos : 0 ≤ᵐ[volume.restrict (Ioi 0)] (fun t : ℝ => ((4*Real.exp 64)*(m+1))*(t^m*Real.exp (-t^2/64))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    positivity
  have hbound : (∫⁻ x, ENNReal.ofReal (Z x^(m+1)) ∂μ) ≤ ENNReal.ofReal (gaussianMomentMajorant m) := by
    have he := lintegral_rpow_eq_lintegral_meas_lt_mul μ (ae_of_all _ hZ0) hZ.aemeasurable (p := (m+1:ℕ)) (by positivity)
    simp only [Real.rpow_natCast] at he
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at he
    rw [he]
    calc
      _ ≤ ENNReal.ofReal ((m:ℝ)+1) * ∫⁻ t : ℝ in Ioi 0,
          ENNReal.ofReal ((4*Real.exp 64)*Real.exp (-t^2/64))*ENNReal.ofReal (t^(m:ℝ)) := by
        apply mul_le_mul' le_rfl
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        apply mul_le_mul' _ le_rfl
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact ENNReal.ofReal_le_ofReal (htail t ht.le)
      _ = ENNReal.ofReal (gaussianMomentMajorant m) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp only [Real.rpow_natCast]
        simp only [← ENNReal.ofReal_mul (by positivity : 0 ≤ (4:ℝ)*Real.exp 64*Real.exp _)]
        simp only [← ENNReal.ofReal_mul (by positivity : 0 ≤ (m:ℝ)+1)]
        have heq : ∀ t : ℝ, ((m:ℝ)+1)*((4*Real.exp 64*Real.exp (-t^2/64))*t^m) =
            ((4*Real.exp 64)*(m+1))*(t^m*Real.exp (-t^2/64)) := by intro t; ring
        simp_rw [heq]
        rw [ ← ofReal_integral_eq_lintegral_ofReal hi' hpos]
        congr 1
        exact integral_const_mul _ _
  have hint : Integrable (fun x => Z x^(m+1)) μ := ⟨(hZ.pow_const _).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => pow_nonneg (hZ0 x) _))).mpr (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  have hnn : 0 ≤ ∫ x, Z x^(m+1) ∂μ := integral_nonneg (fun x => pow_nonneg (hZ0 x) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun x => pow_nonneg (hZ0 x) _))] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (gaussianMomentMajorant_nonneg m)).mp hbound
 theorem gueMatrix_norm_moment {n d : ℕ} (hd : 0 < d) (i : Fin n) (m : ℕ) :
    Integrable (fun x => matrixOpNorm (gueMatrix x i)^(m+1)) (productGaussian (MatrixIndex n d)) ∧
    (∫ x, matrixOpNorm (gueMatrix x i)^(m+1) ∂productGaussian (MatrixIndex n d)) ≤ gaussianMomentMajorant m :=
  tail_power_integral _ (gueMatrix_norm_measurable i) (fun _ => norm_nonneg _) (fun _ ht => gueMatrix_norm_tail_uniform hd i ht) m
end FiniteEntropySeparation

end

end OAI
