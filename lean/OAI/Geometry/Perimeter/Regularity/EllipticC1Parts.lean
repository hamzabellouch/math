import OAI.Geometry.Perimeter.Regularity.EllipticCurl

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
theorem scalar_compact_integration_parts_C1 {n : ℕ} {u v : Euc n → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (hcv : HasCompactSupport v)
    (a : Euc n) :
    Integrable (fun x ↦ u x * fderiv ℝ v x a) volume ∧
    Integrable (fun x ↦ fderiv ℝ u x a * v x) volume ∧
    (∫ x, u x * fderiv ℝ v x a) = -(∫ x, fderiv ℝ u x a * v x) := by
  have hdu : Continuous (fun x ↦ fderiv ℝ u x a) :=
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdv : Continuous (fun x ↦ fderiv ℝ v x a) :=
    (hv.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdv : HasCompactSupport (fun x ↦ fderiv ℝ v x a) :=
    hcv.fderiv_apply ℝ a
  have h1 : Integrable (fun x ↦ u x * fderiv ℝ v x a) volume :=
    (hu.continuous.mul hdv).integrable_of_hasCompactSupport hcdv.mul_left
  have h2 : Integrable (fun x ↦ fderiv ℝ u x a * v x) volume :=
    (hdu.mul hv.continuous).integrable_of_hasCompactSupport hcv.mul_left
  refine ⟨h1, h2, ?_⟩
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h2 h1
    ((hu.continuous.mul hv.continuous).integrable_of_hasCompactSupport hcv.mul_left)
    (fun x _ ↦ hu.differentiable (by simp) x)
    (fun x _ ↦ hv.differentiable (by simp) x)

theorem integral_mul_divergence_eq_neg_inner_gradient_C1 {n : ℕ} {u : Euc n → ℝ}
    {V : Euc n → Euc n} (hu : ContDiff ℝ 1 u)
    (hV : ContDiff ℝ 1 V) (hcV : HasCompactSupport V) :
    (∫ x, u x * divergence V x) = - ∫ x, inner ℝ (gradient u x) (V x) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let v : Fin n → Euc n → ℝ := fun i x ↦ inner ℝ (b i) (V x)
  have hv : ∀ i, ContDiff ℝ 1 (v i) := fun i ↦ (innerSL ℝ (b i)).contDiff.comp hV
  have hcv : ∀ i, HasCompactSupport (v i) := fun i ↦ hcV.comp_left (by simp)
  have hdv : ∀ i x, fderiv ℝ (v i) x (b i) =
      inner ℝ (b i) (fderiv ℝ V x (b i)) := by
    intro i x
    have h := ((innerSL ℝ (b i)).hasFDerivAt.comp x
      (hV.differentiable (by simp) x).hasFDerivAt).fderiv
    exact congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L (b i)) h
  have hp := fun i ↦ scalar_compact_integration_parts_C1 hu (hv i) (hcv i) (b i)
  have hInt1 := fun i ↦ (hp i).2.1
  have hInt2 := fun i ↦ (hp i).1
  have hparts := fun i ↦ (hp i).2.2
  calc
    (∫ x, u x * divergence V x) = ∫ x, ∑ i, u x * fderiv ℝ (v i) x (b i) := by
      congr 1
      funext x
      simp only [divergence, hdv, Finset.mul_sum, b]
    _ = ∑ i, ∫ x, u x * fderiv ℝ (v i) x (b i) := integral_finsetSum _ (fun i _ ↦ hInt2 i)
    _ = -(∑ i, ∫ x, fderiv ℝ u x (b i) * v i x) := by simp only [hparts, Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i, fderiv ℝ u x (b i) * v i x) := by
      rw [integral_finsetSum _ (fun i _ ↦ hInt1 i)]
    _ = -(∫ x, inner ℝ (gradient u x) (V x)) := by
      congr 1
      apply integral_congr_ae
      apply ae_of_all
      intro x
      simp only [← inner_gradient_left, v]
      exact b.sum_inner_mul_inner _ _

theorem gradient_continuous_C1 {n : ℕ} {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) :=
  (InnerProductSpace.toDual ℝ (Euc n)).symm.continuous.comp (hf.continuous_fderiv (by norm_num))

theorem C1_gradient_curl_pairing_zero {n : ℕ} {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f)
    {U : Set (Euc n)} (φ : SmoothLocalTest U) (a b : Euc n) :
    (∫ x, inner ℝ (gradient f x) (curlTest φ.val a b x))=0 := by
  have hi := integral_mul_divergence_eq_neg_inner_gradient_C1 hf
    ((curlTest_contDiff φ.property.1 a b).of_le (by simp))
    (φ.property.2.1.of_isClosed_subset (isClosed_tsupport _) (curlTest_tsupport _ _ _))
  rw [curlTest_divergence φ.property.1] at hi
  simpa only [Pi.zero_apply,mul_zero,integral_zero,eq_neg_iff_add_eq_zero,zero_add] using hi

end RPISingularHarnack

end

end OAI
