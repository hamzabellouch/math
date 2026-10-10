import OAI.MeasureTheory.Falconer.Fourier.MaskedFourier
import OAI.MeasureTheory.Falconer.Estimates.ScaledInverseRemainder

namespace OAI

/-! # The weighted distance law for two different endpoint profiles

Both original marginal laws and their separate normalizations are retained.
The endpoint factors may be the actual descriptor products of different
regularized classes. No common probability law is introduced.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def endpointDistanceWeight {d : ℕ} (s : ℝ)
    (B C : Space d → Space d → ℝ) (z : Space d × Space d) : ℝ :=
  (dist z.1 z.2/s)^(-(((d:ℝ)-1)/2)) *
    B z.1 (NormedSpace.normalize (z.1-z.2)) * C z.2 (NormedSpace.normalize (z.1-z.2))

noncomputable def endpointWeightedDistance {d : ℕ} (μ ν : Measure (Space d))
    (M P s : ℝ) (B C : Space d → Space d → ℝ) : Measure ℝ :=
  ((μ.prod ν).withDensity (fun z => ENNReal.ofReal
    ((M⁻¹*P⁻¹)*endpointDistanceWeight s B C z))).map (fun z => dist z.1 z.2)

 theorem endpointDistanceWeight_measurable {d : ℕ} (s : ℝ)
    (B C : Space d → Space d → ℝ)
    (hB : Measurable (Function.uncurry B)) (hC : Measurable (Function.uncurry C)) :
    Measurable (endpointDistanceWeight s B C) := by
  have hn : Measurable (fun z : Space d × Space d => NormedSpace.normalize (z.1-z.2)) := by
    unfold NormedSpace.normalize
    fun_prop
  exact (((measurable_fst.dist measurable_snd).div_const s).pow_const _).mul
    (hB.comp (measurable_fst.prodMk hn)) |>.mul (hC.comp (measurable_snd.prodMk hn))

 theorem endpointDistanceWeight_nonneg {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (B C : Space d → Space d → ℝ)
    (hB : ∀ x w, 0 ≤ B x w) (hC : ∀ x w, 0 ≤ C x w) (z : Space d × Space d) :
    0 ≤ endpointDistanceWeight s B C z :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg dist_nonneg hs) _) (hB _ _)) (hC _ _)

 theorem endpointDistanceWeight_bound {d : ℕ} (hd : 1 ≤ d) {s δ : ℝ} (hδ : 0 < δ)
    (B C : Space d → Space d → ℝ)
    (hB : ∀ x w, B x w ∈ Icc (0:ℝ) 1) (hC : ∀ x w, C x w ∈ Icc (0:ℝ) 1)
    (z : Space d × Space d) (hz : δ ≤ dist z.1 z.2/s) :
    endpointDistanceWeight s B C z ≤ δ^(-(((d:ℝ)-1)/2)) := by
  have hr : 0 ≤ (dist z.1 z.2/s)^(-(((d:ℝ)-1)/2)) := Real.rpow_nonneg (hδ.trans_le hz).le _
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  apply (mul_le_of_le_one_right (mul_nonneg hr (hB _ _).1) (hC _ _).2).trans
  exact (mul_le_of_le_one_right hr (hB _ _).2).trans
    (Real.rpow_le_rpow_of_nonpos hδ hz (by linarith))

 theorem endpointWeightedDistance_finite {d : ℕ} (hd : 1 ≤ d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P s δ : ℝ} (hM : 0 < M) (hP : 0 < P) (hδ : 0 < δ)
    (B C : Space d → Space d → ℝ)
    (hB : ∀ x w, B x w ∈ Icc (0:ℝ) 1) (hC : ∀ x w, C x w ∈ Icc (0:ℝ) 1)
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) :
    IsFiniteMeasure (endpointWeightedDistance μ ν M P s B C) := by
  have hbound : ∀ᵐ z ∂μ.prod ν,
      ENNReal.ofReal ((M⁻¹*P⁻¹)*endpointDistanceWeight s B C z) ≤
        ENNReal.ofReal ((M⁻¹*P⁻¹)*δ^(-(((d:ℝ)-1)/2))) := by
    filter_upwards [hsep] with z hz
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (endpointDistanceWeight_bound hd hδ B C hB hC z hz) (by positivity))
  let := finite_withDensity_of_bounded (μ.prod ν) _ ENNReal.ofReal_lt_top hbound
  unfold endpointWeightedDistance
  infer_instance

 theorem endpointWeightedDistance_fourier (n : ℕ)
    (μ ν : Measure (Space (n+3))) {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    {s : ℝ} (hs : 0 < s) (B C : Space (n+3) → Space (n+3) → ℝ)
    (hB : Measurable (Function.uncurry B)) (hC : Measurable (Function.uncurry C))
    (hB0 : ∀ x w, 0 ≤ B x w) (hC0 : ∀ x w, 0 ≤ C x w) (r : ℝ) :
    charFun (endpointWeightedDistance μ ν M P s B C) r =
      (M⁻¹*P⁻¹) • ∫ z, scaledDistanceKernel n s r
        (fun x y w => (B x w : ℂ)*(C y w : ℂ)) z ∂μ.prod ν := by
  rw [charFun_apply_real,endpointWeightedDistance,integral_map (by fun_prop) (by fun_prop)]
  have hw : Measurable (fun z => ENNReal.ofReal
      ((M⁻¹*P⁻¹)*endpointDistanceWeight s B C z)) :=
    ((endpointDistanceWeight_measurable s B C hB hC).const_mul _).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hw
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),← integral_smul]
  apply integral_congr_ae
  filter_upwards with z
  rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity)
    (endpointDistanceWeight_nonneg hs.le B C hB0 hC0 z))]
  have he : -((((n+3:ℕ):ℝ)-1)/2) = -(((n+2:ℕ):ℝ)/2) := by push_cast; ring
  simp only [endpointDistanceWeight,scaledDistanceKernel,he,Complex.real_smul,Complex.ofReal_mul]
  push_cast
  ring_nf

end Falconer

end OAI
