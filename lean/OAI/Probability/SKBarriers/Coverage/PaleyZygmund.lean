import Mathlib

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem paleyZygmund_half {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hfpos : ∀ x, 0 ≤ f x)
    (hfi : Integrable f μ) (hf2 : Integrable (fun x => f x^2) μ)
    (hm : 0 < ∫ x, f x ∂μ) :
    (∫ x, f x ∂μ)^2/(4*(∫ x, f x^2 ∂μ)) ≤
      μ.real {x | (∫ y, f y ∂μ)/2 ≤ f x} := by
  let A := {x | (∫ y, f y ∂μ)/2 ≤ f x}
  have hA : MeasurableSet A := measurableSet_le measurable_const hf
  have hAlow : (∫ x, f x ∂μ)/2 ≤ ∫ x in A, f x ∂μ := by
    have H : (∫ x in Aᶜ, f x ∂μ) ≤ (∫ x, f x ∂μ)/2 := by
      calc
        _ ≤ ∫ _x in Aᶜ, (∫ y, f y ∂μ)/2 ∂μ :=
          setIntegral_mono_on hfi.integrableOn (integrable_const _) hA.compl
            (fun x hx => (not_le.mp (show ¬ (∫ y, f y ∂μ)/2 ≤ f x from hx)).le)
        _ = μ.real Aᶜ * ((∫ y, f y ∂μ)/2) := by simp [integral_const]
        _ ≤ (∫ y, f y ∂μ)/2 := by
          have hp : μ.real Aᶜ ≤ 1 := measureReal_le_one
          nlinarith [measureReal_nonneg (μ := μ) (s := Aᶜ)]
    have Hadd := integral_add_compl hA hfi
    linarith
  have hLp : MemLp f 2 (μ.restrict A) :=
    (memLp_two_iff_integrable_sq hfi.integrableOn.aestronglyMeasurable).2 hf2.integrableOn
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all (μ.restrict A) hfpos)
    (ae_of_all (μ.restrict A) (fun _ => show (0:ℝ) ≤ 1 by norm_num))
    (by simpa using hLp)
    (by simpa using (memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) 2 (μ.restrict A)))
  simp only [mul_one,Real.rpow_two,one_pow,integral_const,smul_eq_mul,mul_one,
    measureReal_restrict_apply_univ,
    ← Real.sqrt_eq_rpow] at H
  have hmon : (∫ x in A, f x^2 ∂μ) ≤ ∫ x, f x^2 ∂μ := by
    have Hadd := integral_add_compl hA hf2
    have hc : 0 ≤ ∫ x in Aᶜ, f x^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    linarith
  have hroot : Real.sqrt (∫ x in A, f x^2 ∂μ) ≤ Real.sqrt (∫ x, f x^2 ∂μ) :=
    Real.sqrt_le_sqrt hmon
  have Hfull := H.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _))
  have hepos : 0 ≤ ∫ x, f x^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hppos : 0 ≤ μ.real A := measureReal_nonneg
  have he := Real.sq_sqrt hepos
  have hp := Real.sq_sqrt hppos
  have hnonneg : 0 ≤ Real.sqrt (∫ x, f x^2 ∂μ)*Real.sqrt (μ.real A) := by positivity
  have hmroot : (∫ x, f x ∂μ)/2 ≤
      Real.sqrt (∫ x, f x^2 ∂μ)*Real.sqrt (μ.real A) := hAlow.trans Hfull
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ (∫ x, f x ∂μ)/2) hmroot
  have hrootsq : (Real.sqrt (∫ x, f x^2 ∂μ)*Real.sqrt (μ.real A))^2 =
      (∫ x, f x^2 ∂μ)*μ.real A := by rw [mul_pow,he,hp]
  have Hsq : (∫ x, f x ∂μ)^2 ≤ 4*(∫ x, f x^2 ∂μ)*μ.real A := by nlinarith
  have hegt : 0 < ∫ x, f x^2 ∂μ := by
    by_contra h
    have hz : (∫ x, f x^2 ∂μ) = 0 := le_antisymm (not_lt.mp h) hepos
    rw [hz] at Hsq
    nlinarith
  exact (div_le_iff₀ (by positivity : 0 < 4*(∫ x, f x^2 ∂μ))).mpr (by simpa only [mul_comm] using Hsq)

end SK.Analytic

end
end

end

end OAI
