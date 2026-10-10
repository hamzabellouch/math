import Mathlib
import OAI.Computability.MinUncut.Model

namespace OAI

section
noncomputable section
open MeasureTheory Set
namespace MinUncut.FiniteGaussian

lemma conditional_rounding_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω} (hs : MeasurableSet s)
    (hp : 0 < μ.real s) {F G : Ω → ℝ} (hF : Integrable F μ) (hG : Integrable G μ)
    (hFrange : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hGrange : ∀ x, 0 ≤ G x ∧ G x ≤ 1) :
    |(∫ x, F x ∂μ)-(∫ x in s, G x ∂μ)/μ.real s| ≤
      μ.real sᶜ+∫ x in s, |F x-G x| ∂μ := by
  let p := μ.real s
  let a := μ.real sᶜ
  let B := ∫ x in sᶜ, F x ∂μ
  let C := ∫ x in s, G x ∂μ
  let A := ∫ x in s, F x-G x ∂μ
  have ha : 0 ≤ a := measureReal_nonneg
  have hpa : p+a=1 := by simpa only [p,a,probReal_univ] using measureReal_add_measureReal_compl (μ := μ) hs
  have hB0 : 0 ≤ B := integral_nonneg (fun x => (hFrange x).1)
  have hBa : B ≤ a := by
    have hh := integral_mono hF.integrableOn (integrable_const (1:ℝ)) (fun x => (hFrange x).2) (μ := μ.restrict sᶜ)
    simpa only [setIntegral_const,smul_eq_mul,mul_one] using hh
  have hC0 : 0 ≤ C := integral_nonneg (fun x => (hGrange x).1)
  have hCp : C ≤ p := by
    have hh := integral_mono hG.integrableOn (integrable_const (1:ℝ)) (fun x => (hGrange x).2) (μ := μ.restrict s)
    simpa only [setIntegral_const,smul_eq_mul,mul_one] using hh
  have hratio : 0 ≤ a*C/p := by dsimp [p]; positivity
  have hratiole : a*C/p ≤ a := by
    apply (div_le_iff₀ hp).mpr
    exact mul_le_mul_of_nonneg_left hCp ha
  have hbound : |B-a*C/p| ≤ a := abs_le.mpr ⟨by linarith,by linarith⟩
  have he : (∫ x, F x ∂μ)-C/p=A+(B-a*C/p) := by
    have hsplit := integral_add_compl hs hF
    have hsub := integral_sub hF.integrableOn hG.integrableOn (μ := μ.restrict s)
    change A=(∫ x in s, F x ∂μ)-C at hsub
    have hx : C-C/p= -(a*C/p) := by
      have hp0 : p ≠ 0 := ne_of_gt hp
      apply (mul_right_cancel₀ hp0)
      field_simp [hp0]
      nlinarith
    rw [← hsplit]
    change (∫ x in s, F x ∂μ)+B-C/p=A+(B-a*C/p)
    rw [hsub]
    linear_combination hx
  change |(∫ x, F x ∂μ)-C/p| ≤ a+_
  rw [he]
  have hA : |A| ≤ ∫ x in s, |F x-G x| ∂μ := abs_integral_le_integral_abs
  exact (abs_add_le _ _).trans (by linarith)

end MinUncut.FiniteGaussian

end
end

end OAI
