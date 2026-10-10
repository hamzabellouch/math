import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! The restricted L1 estimate needed for mask removal, derived from
an actual weak (2,2) distribution estimate by layer cake. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem lintegral_inverse_square_tail (K t : ℝ) (ht : 0 < t) :
    (∫⁻ s in Ioi t, ENNReal.ofReal (K^2/s^2)) = ENNReal.ofReal (K^2/t) := by
  have hpow (s : ℝ) : s^(-2:ℝ) = (s^2)⁻¹ := by
    rw [Real.rpow_neg_ofNat]
    simp
  have hfun : (fun s : ℝ => K^2/s^2) = fun s => K^2*s^(-2:ℝ) := by
    funext s
    rw [hpow, div_eq_mul_inv]
  have hi : IntegrableOn (fun s : ℝ => K^2/s^2) (Ioi t) volume := by
    rw [hfun]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) ht).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun s => div_nonneg (sq_nonneg K) (sq_nonneg s)))]
  rw [hfun, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) ht]
  norm_num [Real.rpow_neg_one, div_eq_mul_inv]

theorem weak_two_lintegral_split {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : AEMeasurable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (K t : ℝ) (ht : 0 < t)
    (hweak : ∀ s : ℝ, 0 < s → μ {x | s < f x} ≤ ENNReal.ofReal (K^2/s^2)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal t*μ univ+ENNReal.ofReal (K^2/t) := by
  rw [lintegral_eq_lintegral_meas_lt μ hf0 hf,
    ← Ioc_union_Ioi_eq_Ioi ht.le]
  calc
    _ ≤ (∫⁻ s in Ioc 0 t, μ {x | s < f x}) +
        ∫⁻ s in Ioi t, μ {x | s < f x} := lintegral_union_le _ _ _
    _ ≤ (∫⁻ _s in Ioc 0 t, μ univ) + ∫⁻ s in Ioi t, ENNReal.ofReal (K^2/s^2) := by
      apply add_le_add
      · exact lintegral_mono (fun _ => measure_mono (subset_univ _))
      · exact setLIntegral_mono' measurableSet_Ioi (fun s hs => hweak s (ht.trans hs))
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
        lintegral_inverse_square_tail K t ht, mul_comm (μ univ)]

theorem weak_two_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : μ univ ≠ 0)
    (f : Ω → ℝ) (hf : AEMeasurable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (K : ℝ) (hK : 0 < K)
    (hweak : ∀ s : ℝ, 0 < s → μ {x | s < f x} ≤ ENNReal.ofReal (K^2/s^2)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤
      ENNReal.ofReal (2*K*Real.sqrt ((μ univ).toReal)) := by
  let M := (μ univ).toReal
  have hM : 0 < M := ENNReal.toReal_pos hμ (measure_ne_top μ univ)
  have hS : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  have ht : 0 < K/Real.sqrt M := div_pos hK hS
  have hm : μ univ = ENNReal.ofReal M := (ENNReal.ofReal_toReal (measure_ne_top μ univ)).symm
  have h := weak_two_lintegral_split μ f hf hf0 K (K/Real.sqrt M) ht hweak
  rw [hm, ← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_add (by positivity) (by positivity)] at h
  have heq : K/Real.sqrt M*M+K^2/(K/Real.sqrt M) = 2*K*Real.sqrt M := by
    field_simp
    nlinarith [Real.sq_sqrt hM.le]
  exact h.trans_eq (congrArg ENNReal.ofReal heq)

end LipschitzHilbert

end

end OAI
