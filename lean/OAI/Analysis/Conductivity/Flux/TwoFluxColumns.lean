import Mathlib
import OAI.Analysis.Conductivity.Variational.SmoothSupportedAdd

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem smooth_integration_by_parts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (v : E) (f g : SmoothScalar E) (hf : HasCompactSupport f.val) :
    (∫ x, f.val x * (smoothDirection v g).val x ∂μ) =
      -(∫ x, (smoothDirection v f).val x * g.val x ∂μ) := by
  have hc (a b : SmoothScalar E) (ha : HasCompactSupport a.val) :
      Integrable (fun x => a.val x * b.val x) μ :=
    ((smoothScalar_contDiff a).continuous.mul (smoothScalar_contDiff b).continuous).integrable_of_hasCompactSupport ha.mul_right
  exact integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (hc (smoothDirection v f) g (compactSupport_smoothDirection v hf))
    (hc f (smoothDirection v g) hf) (hc f g hf)
    (fun x _ => ((smoothScalar_contDiff f).differentiable (by simp) x).hasFDerivAt)
    (fun x _ => ((smoothScalar_contDiff g).differentiable (by simp) x).hasFDerivAt)

theorem smooth_divergence_zero_pairing
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (v : ι → E) (F : ι → SmoothScalar E)
    (hF : ∀ i, HasCompactSupport (F i).val)
    (hdiv : ∑ i, smoothDirection (v i) (F i) = 0) (ψ : SmoothScalar E) :
    (∫ x, ∑ i, (F i).val x * (smoothDirection (v i) ψ).val x ∂μ) = 0 := by
  have hI (i : ι) : Integrable (fun x => (F i).val x *
      (smoothDirection (v i) ψ).val x) μ :=
    ((smoothScalar_contDiff (F i)).continuous.mul
      (smoothScalar_contDiff (smoothDirection (v i) ψ)).continuous).integrable_of_hasCompactSupport (hF i).mul_right
  have hI' (i : ι) : Integrable (fun x => (smoothDirection (v i) (F i)).val x *
      ψ.val x) μ :=
    ((smoothScalar_contDiff (smoothDirection (v i) (F i))).continuous.mul
      (smoothScalar_contDiff ψ).continuous).integrable_of_hasCompactSupport
        (compactSupport_smoothDirection (v i) (hF i)).mul_right
  rw [integral_finsetSum _ (fun i _ => hI i)]
  simp_rw [smooth_integration_by_parts μ _ _ _ (hF _)]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hI' i)]
  have hz (x : E) : ∑ i, (smoothDirection (v i) (F i)).val x = 0 := by
    have hh := congrArg (fun f : SmoothScalar E => f.val x) hdiv
    simpa using hh
  simp_rw [← Finset.sum_mul, hz, zero_mul]
  simp

def twoFluxColumns {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : Fin 5 → SmoothScalar E) : Fin 2 → Fin 3 → SmoothScalar E :=
  ![![G 0, G 1, G 3], ![G 1, G 2, G 4]]

theorem twoFluxColumns_divergence {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : Fin 3 → E) (G : Fin 5 → SmoothScalar E) (j : Fin 2) :
    ∑ i, smoothDirection (v i) (twoFluxColumns G j i) = twoFluxDivergence v G j := by
  fin_cases j <;> simp [twoFluxColumns, twoFluxDivergence, Fin.sum_univ_succ, add_assoc]

theorem localizedTwoFlux_weak_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (v : Fin 3 → E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H₁ H₂ : SmoothScalar ℝ) (α p q r k : ℝ) (hχ : HasCompactSupport χ.val)
    (j : Fin 2) (ψ : SmoothScalar E) :
    (∫ x, ∑ i, (twoFluxColumns (localizedTwoFlux v χ L H₁ H₂ α p q r k) j i).val x *
        (smoothDirection (v i) ψ).val x ∂μ) = 0 := by
  apply smooth_divergence_zero_pairing μ v _ _ _ ψ
  · have hc (i : Fin 5) : HasCompactSupport
        (localizedTwoFlux v χ L H₁ H₂ α p q r k i).val :=
      hχ.of_isClosed_subset (isClosed_tsupport _)
        (localizedTwoFlux_support v χ L H₁ H₂ α p q r k i)
    intro i
    fin_cases j <;> fin_cases i <;> exact hc _
  · rw [twoFluxColumns_divergence, localizedTwoFlux_divergence]
    rfl

def piolaFlux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E ≃ E) (F : E → E) (y : E) : E :=
  |(fderiv ℝ X (X.symm y)).det|⁻¹ • fderiv ℝ X (X.symm y) (F (X.symm y))

theorem piolaFlux_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : E ≃ E) (hX : Differentiable ℝ X)
    (hdet : ∀ x, (fderiv ℝ X x).det ≠ 0)
    (F : E → E) (ψ : E → ℝ) (hψ : Differentiable ℝ ψ) :
    (∫ y, fderiv ℝ ψ y (piolaFlux X F y) ∂μ) =
      ∫ x, fderiv ℝ (ψ ∘ X) x (F x) ∂μ := by
  have hc := integral_image_eq_integral_abs_det_fderiv_smul μ
    MeasurableSet.univ (fun x _ => (hX x).hasFDerivAt.hasFDerivWithinAt)
    X.injective.injOn (fun y => fderiv ℝ ψ y (piolaFlux X F y))
  simp only [Set.image_univ, Set.range_eq_univ.mpr X.surjective, Measure.restrict_univ] at hc
  rw [hc]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [piolaFlux, X.symm_apply_apply, map_smul, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr (hdet x)), one_mul]
  rw [fderiv_comp x (hψ _) (hX x)]
  rfl

end ScalarConductivity

end

end OAI
