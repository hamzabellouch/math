import OAI.Analysis.KadisonKastler.PoissonProductEstimates
import OAI.Analysis.KadisonKastler.DemodulatedCharacter
import OAI.Analysis.KadisonKastler.HardyPoissonProducts

namespace OAI

/-! # Approximate inverses after Poisson demodulation

The Hardy product identity follows from the published evaluation input
on the concrete positive-frequency algebra. The scalar Poisson character
formula is proved, and inverse estimates use the actual boundary product.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem norm_demodulatedPoisson_product_sub_one_le_of_product_identity
    (B S U V : ℝ → H →L[ℂ] H)
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x) volume)
    (hS : ∀ x, AEStronglyMeasurable (fun s => S s x) volume)
    (hU : ∀ x, AEStronglyMeasurable (fun s => U s x) volume)
    (hV : ∀ x, AEStronglyMeasurable (fun s => V s x) volume)
    {CB CS : ℝ}
    (hb : ∀ᵐ s, ‖B s‖ ≤ CB) (hs : ∀ᵐ s, ‖S s‖ ≤ CS)
    (hBS : ∀ᵐ s, ‖B s * S s‖ ≤ CB * CS)
    (hUV : ∀ᵐ s, ‖U s * V s‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : ∀ᵐ s, ‖U s‖ ≤ 1) (hv : ∀ᵐ s, ‖V s‖ ≤ 1)
    (hBU : ∀ᵐ s, ‖B s - U s‖ ≤ δ) (hSV : ∀ᵐ s, ‖S s - V s‖ ≤ δ)
    (t r : ℝ) (hr : 0 < r)
    (hproduct : measurablePoissonAverage B hB CB hb t r hr *
        measurablePoissonAverage S hS CS hs t r hr =
      measurablePoissonAverage (fun s => B s * S s)
        (operator_product_vector_measurable B S hB hS) (CB * CS) hBS t r hr)
    (hboundary : ∀ᵐ s, U s * V s = poissonCharacterField 2 s) :
    ‖demodulatedPoissonAverage B hB CB hb t r hr *
        demodulatedPoissonAverage S hS CS hs t r hr - 1‖ ≤
      Real.exp (2 * r) * (2 * δ + δ ^ 2) := by
  have hphase := measurablePoissonAverage_phase_cancel (fun s => U s * V s)
    (operator_product_vector_measurable U V hU hV) 1 hUV hboundary t r hr
  let z : ℂ := (Real.exp r : ℂ) * star (Circle.exp t : ℂ)
  have hz : ‖z‖ = Real.exp r := by
    change ‖(Real.exp r : ℂ) * star (Circle.exp t : ℂ)‖ = Real.exp r
    rw [norm_mul, norm_star, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos r)]
  have herror := norm_measurablePoissonAverage_sub_le
    (fun s => B s * S s) (fun s => U s * V s)
    (operator_product_vector_measurable B S hB hS)
    (operator_product_vector_measurable U V hU hV)
    (CB * CS) 1 hBS hUV (by positivity)
    (ae_product_error B S U V hδ hu hv hBU hSV) t r hr
  have hid : demodulatedPoissonAverage B hB CB hb t r hr *
        demodulatedPoissonAverage S hS CS hs t r hr - 1 =
      z ^ 2 • (measurablePoissonAverage (fun s => B s * S s)
          (operator_product_vector_measurable B S hB hS) (CB * CS) hBS t r hr -
        measurablePoissonAverage (fun s => U s * V s)
          (operator_product_vector_measurable U V hU hV) 1 hUV t r hr) := by
    rw [smul_sub, hphase]
    unfold demodulatedPoissonAverage
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hproduct]
    simp only [z, pow_two]
  rw [hid, norm_smul, norm_pow, hz]
  have he : (Real.exp r) ^ 2 = Real.exp (2 * r) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left herror (Real.exp_pos _).le


theorem norm_demodulatedPoisson_product_sub_one_le
    [TopologicalSpace.SeparableSpace H]
    (hHardy : PublishedHardyMultiplierEvaluation.{u})
    (B S U V : ℝ → H →L[ℂ] H)
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x) volume)
    (hS : ∀ x, AEStronglyMeasurable (fun s => S s x) volume)
    (hU : ∀ x, AEStronglyMeasurable (fun s => U s x) volume)
    (hV : ∀ x, AEStronglyMeasurable (fun s => V s x) volume)
    {CB CS : ℝ}
    (hb : ∀ᵐ s, ‖B s‖ ≤ CB) (hs : ∀ᵐ s, ‖S s‖ ≤ CS)
    (hBS : ∀ᵐ s, ‖B s * S s‖ ≤ CB * CS)
    (hUV : ∀ᵐ s, ‖U s * V s‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : ∀ᵐ s, ‖U s‖ ≤ 1) (hv : ∀ᵐ s, ‖V s‖ ≤ 1)
    (hBU : ∀ᵐ s, ‖B s - U s‖ ≤ δ) (hSV : ∀ᵐ s, ‖S s - V s‖ ≤ δ)
    (t r : ℝ) (hr : 0 < r)
    (hBpres : PreservesProjectionNest (regularFrequencyNest (H := H))
      (regularFieldOperator volume B hB CB hb))
    (hSpres : PreservesProjectionNest (regularFrequencyNest (H := H))
      (regularFieldOperator volume S hS CS hs))
    (hboundary : ∀ᵐ s, U s * V s = poissonCharacterField 2 s) :
    ‖demodulatedPoissonAverage B hB CB hb t r hr *
        demodulatedPoissonAverage S hS CS hs t r hr - 1‖ ≤
      Real.exp (2 * r) * (2 * δ + δ ^ 2) := by
  let TB : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    regularFieldOperator volume B hB CB hb
  let TS : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    regularFieldOperator volume S hS CS hs
  have hBT : RepresentsOperatorField volume B TB := regularFieldOperator_represents volume B hB CB hb
  have hST : RepresentsOperatorField volume S TS := regularFieldOperator_represents volume S hS CS hs
  have hproduct := measurablePoissonAverage_mul_of_hardy hHardy B S hB hS CB CS hb hs hBS
    TB TS hBT hST hBpres hSpres t r hr
  exact norm_demodulatedPoisson_product_sub_one_le_of_product_identity
    B S U V hB hS hU hV hb hs hBS hUV hδ hu hv hBU hSV t r hr hproduct hboundary
/-- A small boundary error and a no-larger positive height give a linear
inverse error with an absolute constant. -/
theorem exp_two_mul_product_error_le {r δ : ℝ}
    (hr : 0 ≤ r) (hrδ : r ≤ δ) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 8) :
    Real.exp (2 * r) * (2 * δ + δ ^ 2) ≤ 6 * δ := by
  have hrsmall : |2 * r| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; linarith
  have he := Real.abs_exp_sub_one_le (x := 2 * r) hrsmall
  have he' : Real.exp (2 * r) ≤ 2 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr)] at he
    linarith [le_abs_self (Real.exp (2 * r) - 1)]
  calc
    Real.exp (2 * r) * (2 * δ + δ ^ 2) ≤ 2 * (2 * δ + δ ^ 2) :=
      mul_le_mul_of_nonneg_right he' (by positivity)
    _ ≤ 6 * δ := by nlinarith

end

end KadisonKastler

end OAI
