import OAI.Probability.InvariantIsing.Fields.FieldFiniteTransformDerivative

namespace OAI

/-! Uniform bounds on the joint gradient and Hessian after one Gaussian
step, independent of the scalar spatial field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma affine_bounded_integral_bound (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {A : ℝ → ℝ} {C : ℝ}
    (hA : ∀ u, |A u| ≤ C) : |∫ u, A u ∂F.affineLaw a v ζ p| ≤ C := by
  have := F.affineLaw_probability a v ζ hp
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := F.affineLaw a v ζ p) (f := A) (C := C)
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hA u)

lemma bound_mean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) : |F.mean a v ζ p| ≤ F.KX :=
  F.affine_bounded_integral_bound a v ζ hp (fun u => F.bX (F.shiftPoint a v u p) hp)

lemma bound_curvature (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    |F.curvature a v ζ p| ≤ F.KXX + 2 * |ζ| * F.KX ^ 2 := by
  have hXX := F.affine_bounded_integral_bound a v ζ hp (fun u => F.bXX (F.shiftPoint a v u p) hp)
  have hprod (u : ℝ) : |F.shiftedMean a v u p * F.shiftedMean a v u p| ≤ F.KX ^ 2 := by
    rw [abs_mul]
    simpa only [pow_two, shiftedMean] using mul_self_le_mul_self (abs_nonneg _)
      (F.bX (F.shiftPoint a v u p) hp)
  have hAvg := F.affine_bounded_integral_bound a v ζ hp hprod
  have hMean : |F.mean a v ζ p * F.mean a v ζ p| ≤ F.KX ^ 2 := by
    rw [abs_mul]
    simpa only [pow_two] using mul_self_le_mul_self (abs_nonneg _)
      (F.bound_mean a v ζ hp)
  unfold curvature
  refine (abs_add_le _ _).trans (add_le_add hXX ?_)
  rw [abs_mul]
  calc
    _ ≤ |ζ| * (F.KX ^ 2 + F.KX ^ 2) :=
      mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hAvg hMean)) (abs_nonneg ζ)
    _ = _ := by ring

lemma affine_linear_integral_bound (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {V : ℝ} (hV : fieldFiniteVariance a v p.1 ≤ V)
    {A : ℝ → ℝ} (hA : Measurable A) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ u, |A u| ≤ C * (1 + |u|)) :
    |∫ u, A u ∂F.affineLaw a v ζ p| ≤ C * F.affineMomentCap ζ V := by
  apply F.affineLaw_integral_bound a v ζ hp hV hA hC
  intro u
  exact (hB u).trans (mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) hC)

def tangentCap (R ζ V : ℝ) : ℝ :=
  (F.KP + F.KX * R) * F.affineMomentCap ζ V

def mixedMeanCap (R ζ V : ℝ) : ℝ :=
  (F.KPX + F.KXX * R + 2 * |ζ| * F.KX * (F.KP + F.KX * R)) *
    F.affineMomentCap ζ V

def secondMeanCap (R D ζ V : ℝ) : ℝ :=
  (F.KPP + 2 * F.KPX * R + F.KXX * R ^ 2 + F.KX * D) * F.affineMomentCap ζ V +
    |ζ| * ((F.KP + F.KX * R) ^ 2 * F.affineMomentCap ζ V +
      ((F.KP + F.KX * R) * F.affineMomentCap ζ V) ^ 2)

lemma bound_tangent (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i : Fin n)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {R V : ℝ} (hR : 0 ≤ R)
    (hc : |fieldFiniteSlope a v p.1 i| ≤ R) (hV : fieldFiniteVariance a v p.1 ≤ V) :
    |F.tangent a v ζ i p| ≤ F.tangentCap R ζ V := by
  have hX := F.kx_nonneg
  have hP := F.kp_nonneg
  exact F.affine_linear_integral_bound a v ζ hp hV
    (F.measurable_shiftedTangent a v i p) (by positivity)
    (fun u => F.shiftedTangent_bound a v i u hp hR hc)

lemma bound_mixedMean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i : Fin n)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {R V : ℝ} (hR : 0 ≤ R)
    (hc : |fieldFiniteSlope a v p.1 i| ≤ R) (hV : fieldFiniteVariance a v p.1 ≤ V) :
    |F.mixedMean a v ζ i p| ≤ F.mixedMeanCap R ζ V := by
  let A := F.KP + F.KX * R
  let B := F.KPX + F.KXX * R
  let M := F.affineMomentCap ζ V
  let ν := F.affineLaw a v ζ p
  have hX := F.kx_nonneg
  have hP := F.kp_nonneg
  have hXX := F.kxx_nonneg
  have hPX := F.kpx_nonneg
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hiA : |F.tangent a v ζ i p| ≤ A * M := F.bound_tangent a v ζ i hp hR hc hV
  have hiB : |∫ u, F.shiftedMixed a v i u p ∂ν| ≤ B * M :=
    F.affine_linear_integral_bound a v ζ hp hV
      (F.measurable_shiftedMixed a v i p) hB
      (fun u => F.shiftedMixed_bound a v i u hp hR hc)
  have hiXA : |∫ u, F.shiftedMean a v u p * F.shiftedTangent a v i u p ∂ν| ≤ F.KX * A * M := by
    apply F.affine_linear_integral_bound a v ζ hp hV
      ((F.measurable_shiftedMean a v p).mul (F.measurable_shiftedTangent a v i p)) (mul_nonneg hX hA)
    intro u
    change |F.shiftedMean a v u p * F.shiftedTangent a v i u p| ≤ _
    rw [abs_mul]
    calc
      _ ≤ F.KX * (A * (1 + |u|)) := mul_le_mul (F.bX (F.shiftPoint a v u p) hp)
        (F.shiftedTangent_bound a v i u hp hR hc) (abs_nonneg _) hX
      _ = _ := by ring
  unfold mixedMean
  calc
    _ ≤ |∫ u, F.shiftedMixed a v i u p ∂ν| +
        |ζ * ((∫ u, F.shiftedMean a v u p * F.shiftedTangent a v i u p ∂ν) -
          F.mean a v ζ p * F.tangent a v ζ i p)| := abs_add_le _ _
    _ ≤ B * M + |ζ| * (F.KX * A * M + F.KX * (A * M)) := by
      apply add_le_add hiB
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg ζ)
      refine (abs_sub _ _).trans (add_le_add hiXA ?_)
      rw [abs_mul]
      exact mul_le_mul (F.bound_mean a v ζ hp) hiA (abs_nonneg _) hX
    _ = _ := by dsimp only [mixedMeanCap, A, B, M]; ring

lemma bound_secondMean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i j : Fin n)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {R D V : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hci : |fieldFiniteSlope a v p.1 i| ≤ R)
    (hcj : |fieldFiniteSlope a v p.1 j| ≤ R)
    (hd : |fieldFiniteCurvature a v p.1 i j| ≤ D)
    (hV : fieldFiniteVariance a v p.1 ≤ V) :
    |F.secondMean a v ζ i j p| ≤ F.secondMeanCap R D ζ V := by
  let A := F.KP + F.KX * R
  let C := F.KPP + 2 * F.KPX * R + F.KXX * R ^ 2 + F.KX * D
  let M := F.affineMomentCap ζ V
  let ν := F.affineLaw a v ζ p
  have hX := F.kx_nonneg
  have hP := F.kp_nonneg
  have hXX := F.kxx_nonneg
  have hPX := F.kpx_nonneg
  have hPP := F.kpp_nonneg
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hM : 0 ≤ M := (F.affineMomentCap_pos ζ V).le
  have hiAi : |F.tangent a v ζ i p| ≤ A * M := F.bound_tangent a v ζ i hp hR hci hV
  have hiAj : |F.tangent a v ζ j p| ≤ A * M := F.bound_tangent a v ζ j hp hR hcj hV
  have hiC : |∫ u, F.shiftedHessian a v i j u p ∂ν| ≤ C * M :=
    F.affineLaw_integral_bound a v ζ hp hV (F.measurable_shiftedHessian a v i j p)
      hC (fun u => F.shiftedHessian_bound a v i j u hp hR hD hci hcj hd)
  have hiAA : |∫ u, F.shiftedTangent a v i u p * F.shiftedTangent a v j u p ∂ν| ≤ A ^ 2 * M := by
    apply F.affineLaw_integral_bound a v ζ hp hV
      ((F.measurable_shiftedTangent a v i p).mul (F.measurable_shiftedTangent a v j p)) (sq_nonneg A)
    intro u
    change |F.shiftedTangent a v i u p * F.shiftedTangent a v j u p| ≤ _
    rw [abs_mul]
    calc
      _ ≤ (A * (1 + |u|)) * (A * (1 + |u|)) :=
        mul_le_mul (F.shiftedTangent_bound a v i u hp hR hci)
          (F.shiftedTangent_bound a v j u hp hR hcj) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hproduct : |F.tangent a v ζ i p * F.tangent a v ζ j p| ≤ (A * M) ^ 2 := by
    rw [abs_mul]
    simpa only [pow_two] using mul_le_mul hiAi hiAj (abs_nonneg _) (mul_nonneg hA hM)
  unfold secondMean
  calc
    _ ≤ |∫ u, F.shiftedHessian a v i j u p ∂ν| +
        |ζ * ((∫ u, F.shiftedTangent a v i u p * F.shiftedTangent a v j u p ∂ν) -
          F.tangent a v ζ i p * F.tangent a v ζ j p)| := abs_add_le _ _
    _ ≤ C * M + |ζ| * (A ^ 2 * M + (A * M) ^ 2) := by
      apply add_le_add hiC
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hiAA hproduct)) (abs_nonneg ζ)
    _ = _ := by dsimp only [secondMeanCap, A, C, M]

end FieldFiniteFamily
end InvariantIsing

end

end OAI
