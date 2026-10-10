import OAI.Geometry.Perimeter.Regularity.EllipticC1Test
import OAI.Geometry.Perimeter.Regularity.EllipticCaccioppoliAlgebra

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem continuous_inner_gradient_integrable {G : Euc n → Euc n} {f : Euc n → ℝ}
    (hG : Continuous G) (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) :
    Integrable (fun x ↦ inner ℝ (G x) (gradient f x)) volume := by
  apply (hG.inner (gradient_continuous_C1 hf)).integrable_of_hasCompactSupport
  apply (gradient_hasCompactSupport hcf).of_isClosed_subset (isClosed_tsupport _)
  apply closure_mono
  intro x hx
  exact fun hz ↦ hx (by simp [hz])

 theorem square_weight_integrable {u : Euc n → ℝ} {G : Euc n → Euc n}
    (hu : Continuous u) (hcu : HasCompactSupport u) (hG : Continuous G) :
    Integrable (fun x ↦ (u x)^2*‖G x‖^2) volume := by
  apply ((hu.pow 2).mul (hG.norm.pow 2)).integrable_of_hasCompactSupport
  apply hcu.of_isClosed_subset (isClosed_tsupport _)
  apply closure_mono
  intro x hx
  exact fun hz ↦ hx (by simp [hz])

 theorem square_compact_field_integrable {u : Euc n → ℝ} {G : Euc n → Euc n}
    (hu : Continuous u) (hG : Continuous G) (hcG : HasCompactSupport G) :
    Integrable (fun x ↦ (u x)^2*‖G x‖^2) volume := by
  apply ((hu.pow 2).mul (hG.norm.pow 2)).integrable_of_hasCompactSupport
  apply hcG.of_isClosed_subset (isClosed_tsupport _)
  apply closure_mono
  intro x hx
  exact fun hz ↦ hx (by simp [hz])

 theorem caccioppoli_test_bound {A : Euc n → Euc n →L[ℝ] Euc n}
    {f : Euc n → ℝ} {F : Euc n → Euc n} (hf : ContDiff ℝ 1 f)
    {p : Euc n} {r : ℝ}
    (hnear : ∀ x∈Metric.ball p r, ‖ContinuousLinearMap.id ℝ (Euc n)-A x‖≤1/2)
    {χ : Euc n → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hsχ : tsupport χ ⊆ Metric.ball p r) (x : Euc n) : (χ x)^2*‖gradient f x‖^2 ≤
    4*inner ℝ (A x (gradient f x)-F x) (gradient (fun y ↦ χ y*χ y*f y) x)+256*((f x)^2*‖gradient χ x‖^2+(χ x)^2*‖F x‖^2) := by
  by_cases hx : x∈tsupport χ
  · rw [gradient_square_test (hf.differentiable (by simp)) (hχ.differentiable (by simp))]
    exact caccioppoli_pointwise (A x) (hnear x (hsχ hx)) (gradient f x) (gradient χ x) (F x) (χ x) (f x)
  · have hχ0 := image_eq_zero_of_notMem_tsupport hx
    have hD0 : gradient χ x=0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (gradient_tsupport_subset χ hh))
    rw [gradient_square_test (hf.differentiable (by simp)) (hχ.differentiable (by simp)),hχ0,hD0]
    simp

 theorem WeakLinearEquation.caccioppoli {A : Euc n → Euc n →L[ℝ] Euc n}
    {f : Euc n → ℝ} {F : Euc n → Euc n} (hA : Continuous A) (hf : ContDiff ℝ 1 f)
    (hF : Continuous F) {p : Euc n} {r : ℝ} (h : WeakLinearEquation A f F (Metric.ball p r))
    (hnear : ∀ x∈Metric.ball p r, ‖ContinuousLinearMap.id ℝ (Euc n)-A x‖≤1/2)
    {χ : Euc n → ℝ} (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Metric.ball p r) :
    (∫ x, (χ x)^2*‖gradient f x‖^2) ≤
      256*((∫ x, (f x)^2*‖gradient χ x‖^2)+(∫ x, (χ x)^2*‖F x‖^2)) := by
  let φ := fun x ↦ χ x*χ x*f x
  have hφ : ContDiff ℝ 1 φ := hχ.mul hχ |>.mul hf
  have hcφ : HasCompactSupport φ := hcχ.mul_right.mul_right
  have hsφ : tsupport φ ⊆ Metric.ball p r :=
    tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans hsχ)
  have hz := h.test_C1 hA hf hF hφ hcφ hsφ
  let J := fun x ↦ inner ℝ (A x (gradient f x)-F x) (gradient φ x)
  have hJ : Integrable J volume := continuous_inner_gradient_integrable
    ((hA.clm_apply (gradient_continuous_C1 hf)).sub hF) hφ hcφ
  have hI := square_weight_integrable hχ.continuous hcχ (gradient_continuous_C1 hf)
  have hI₁ := square_compact_field_integrable hf.continuous (gradient_continuous_C1 hχ)
    (gradient_hasCompactSupport hcχ)
  have hI₂ := square_weight_integrable hχ.continuous hcχ hF
  have hpt := caccioppoli_test_bound (F := F) hf hnear hχ hsχ
  have hh := integral_mono hI ((hJ.const_mul 4).add ((hI₁.add hI₂).const_mul 256)) hpt
  simp only [Pi.add_apply] at hh
  erw [integral_add (hJ.const_mul 4) ((hI₁.add hI₂).const_mul 256),integral_const_mul,
    integral_const_mul,integral_add hI₁ hI₂] at hh
  change (∫ x,J x)=0 at hz
  rw [hz,mul_zero,zero_add] at hh
  exact hh

end RPISingularHarnack

end

end OAI
