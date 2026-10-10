import OAI.Probability.InvariantIsing.Fields.FieldFiniteTransformData

namespace OAI

/-! Joint first and second derivatives of the actual finite-height
Gaussian step, with the Hessian expressed by the tilted covariance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma value_coordinate_derivative (hI : IsOpen I) (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {V R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ t ∈ I, 0 < fieldFiniteVariance a v t)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ i, |fieldFiniteSlope a v t i| ≤ R)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    HasFDerivAt (F.value a v ζ)
      (fieldFiniteLinear (fun i => F.tangent a v ζ i p) (F.mean a v ζ p)) p := by
  have hX := F.kx_nonneg
  have hP := F.kp_nonneg
  have hD := F.value_hasFDerivAt hI a v ζ hR hlo hhi hc hp
  have hiT (i : Fin n) : Integrable (fun u => F.shiftedTangent a v i u p)
      (F.affineLaw a v ζ p) :=
    F.affineLaw_linear_integrable a v ζ hp (F.measurable_shiftedTangent a v i p)
      (by positivity : 0 ≤ F.KP + F.KX * R)
      (fun u => F.shiftedTangent_bound a v i u hp hR (hc p.1 hp i))
  have hiX : Integrable (fun u => F.shiftedMean a v u p) (F.affineLaw a v ζ p) :=
    F.affineLaw_bounded_integrable a v ζ hp (F.measurable_shiftedMean a v p) F.KX
      (fun u => F.bX _ hp)
  change HasFDerivAt _ (∫ u, fieldFiniteLinear (fun i => F.shiftedTangent a v i u p)
    (F.shiftedMean a v u p) ∂F.affineLaw a v ζ p) p at hD
  rw [integral_fieldFiniteLinear _ hiT hiX] at hD
  exact hD

lemma mean_hasFDerivAt (hI : IsOpen I) (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {V R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ t ∈ I, 0 < fieldFiniteVariance a v t)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ i, |fieldFiniteSlope a v t i| ≤ R)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    HasFDerivAt (F.mean a v ζ)
      (fieldFiniteLinear (fun i => F.mixedMean a v ζ i p) (F.curvature a v ζ p)) p := by
  have hX := F.kx_nonneg
  have hXX := F.kxx_nonneg
  have hP := F.kp_nonneg
  have hPX := F.kpx_nonneg
  have hPP := F.kpp_nonneg
  let B := F.KPX + F.KXX * R
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  exact F.affine_average_coordinate_derivative hI
    (fun q u => F.shiftedMean a v u q)
    (fun q u => F.XX (F.shiftPoint a v u q))
    (fun i q u => F.shiftedMixed a v i u q) a v ζ hR hlo hhi hc
    F.kx_nonneg (show 0 ≤ B + F.KXX by positivity)
    (fun q => F.measurable_shiftedMean a v q)
    (fun i q => F.measurable_shiftedMixed a v i q)
    (fun q => F.mXX.comp (by dsimp only [shiftPoint]; fun_prop))
    (fun q hq u => (F.bX (F.shiftPoint a v u q) hq).trans
      (le_mul_of_one_le_right F.kx_nonneg (by linarith [abs_nonneg u])))
    (fun i q hq u => (F.shiftedMixed_bound a v i u hq hR (hc q.1 hq i)).trans (by
      calc
        _ ≤ B * (1 + |u|) ^ 2 :=
          mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) hB
        _ ≤ (B + F.KXX) * (1 + |u|) ^ 2 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right F.kxx_nonneg) (sq_nonneg _)))
    (fun q hq u => (F.bXX (F.shiftPoint a v u q) hq).trans (by
      have hq1 : 1 ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u]
      calc
        F.KXX ≤ F.KXX * (1 + |u|) ^ 2 := le_mul_of_one_le_right F.kxx_nonneg hq1
        _ ≤ (B + F.KXX) * (1 + |u|) ^ 2 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB) (sq_nonneg _)))
    (fun q hq u => F.shiftedMean_hasFDerivAt a v u hq (hlo q.1 hq)) hp

lemma tangent_hasFDerivAt (hI : IsOpen I) (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    (i : Fin n) {V R D : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hlo : ∀ t ∈ I, 0 < fieldFiniteVariance a v t)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ j, |fieldFiniteSlope a v t j| ≤ R)
    (hd : ∀ t ∈ I, ∀ j k, |fieldFiniteCurvature a v t j k| ≤ D)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    HasFDerivAt (F.tangent a v ζ i)
      (fieldFiniteLinear (fun j => F.secondMean a v ζ i j p) (F.mixedMean a v ζ i p)) p := by
  have hX := F.kx_nonneg
  have hXX := F.kxx_nonneg
  have hP := F.kp_nonneg
  have hPX := F.kpx_nonneg
  have hPP := F.kpp_nonneg
  let B := F.KPX + F.KXX * R
  let C := F.KPP + 2 * F.KPX * R + F.KXX * R ^ 2 + F.KX * D
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have h := F.affine_average_coordinate_derivative hI
    (fun q u => F.shiftedTangent a v i u q)
    (fun q u => F.shiftedMixed a v i u q)
    (fun j q u => F.shiftedHessian a v i j u q) a v ζ hR hlo hhi hc
    (show 0 ≤ F.KP + F.KX * R by positivity) (show 0 ≤ B + C by positivity)
    (fun q => F.measurable_shiftedTangent a v i q)
    (fun j q => F.measurable_shiftedHessian a v i j q)
    (fun q => F.measurable_shiftedMixed a v i q)
    (fun q hq u => F.shiftedTangent_bound a v i u hq hR (hc q.1 hq i))
    (fun j q hq u => (F.shiftedHessian_bound a v i j u hq hR hD
      (hc q.1 hq i) (hc q.1 hq j) (hd q.1 hq i j)).trans (by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact le_add_of_nonneg_left hB))
    (fun q hq u => (F.shiftedMixed_bound a v i u hq hR (hc q.1 hq i)).trans (by
      calc
        _ ≤ B * (1 + |u|) ^ 2 :=
          mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) hB
        _ ≤ (B + C) * (1 + |u|) ^ 2 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC) (sq_nonneg _)))
    (fun q hq u => F.shiftedTangent_hasFDerivAt a v i u hq (hlo q.1 hq)) hp
  convert h using 1
  · rfl
  · apply congrArg₂ (fun A B => fieldFiniteLinear A B)
    · rfl
    · unfold mixedMean mean tangent
      rw [show (fun u => F.shiftedMean a v u p * F.shiftedTangent a v i u p) =
          (fun u => F.shiftedTangent a v i u p * F.shiftedMean a v u p) from
          funext (fun u => mul_comm _ _)]
      ring

end FieldFiniteFamily
end InvariantIsing

end

end OAI
