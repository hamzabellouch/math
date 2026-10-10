import OAI.Geometry.Perimeter.Regularity.RawConeLink

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
namespace RPISingularHarnack
namespace SphericalFrankel

lemma angle_swap {n : ℕ} (e f : Frame n) : angle f e = angle e f := real_inner_comm _ _

lemma cross_swap {n : ℕ} (e f : Frame n) : cross f e = cross e f := real_inner_comm _ _

lemma traceProduct_swap {n : ℕ} (e f : Frame n) : traceProduct f e = traceProduct e f := by
  simp only [traceProduct, angle_swap, real_inner_comm f.1 e.2,
    real_inner_comm f.2 e.1, real_inner_comm f.2 e.2]
  ring

lemma continuous_defect_reverse {n : ℕ} :
    Continuous (fun p : Frame n × Frame n ↦ defect p.2 p.1) := by
  unfold defect proj
  fun_prop

lemma product_frames {n : ℕ} {μ ν : Measure (Frame n)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ e ∂μ, IsFrame e) (hν : ∀ᵐ e ∂ν, IsFrame e) :
    ∀ᵐ p ∂μ.prod ν, IsFrame p.1 ∧ IsFrame p.2 := by
  apply (Measure.ae_prod_iff_ae_ae
    ((isClosed_frames n).prod (isClosed_frames n)).measurableSet).mpr
  filter_upwards [hμ] with e he
  filter_upwards [hν] with f hf
  exact ⟨he, hf⟩

lemma stationary_product_integral {n : ℕ} {μ ν : Measure (Frame n)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ e ∂μ, IsFrame e) (hν : ∀ᵐ e ∂ν, IsFrame e)
    (hS : LinkStationary μ) (W : Frame n → Euc n → Euc n)
    (hW : ∀ f, ContDiff ℝ ∞ (W f))
    (G : Frame n × Frame n → ℝ) (hG : Continuous G)
    (heq : ∀ e f, IsFrame e → IsFrame f → G (e,f) = linkDiv e (W f)) :
    (∫ p, G p ∂μ.prod ν) = 0 := by
  rw [integral_prod_symm G (integrable_pairFrameFunction (product_frames hμ hν) hG)]
  calc
    (∫ f, ∫ e, G (e, f) ∂μ ∂ν) = ∫ f, (0 : ℝ) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hν] with f hf
      calc
        (∫ e, G (e,f) ∂μ) = ∫ e, linkDiv e (W f) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hμ] with e he
          exact heq e f he hf
        _ = 0 := hS.firstVariation (W f) (hW f)
    _ = 0 := by simp

lemma stationary_gradient_one {n : ℕ} {μ ν : Measure (Frame n)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ e ∂μ, IsFrame e) (hν : ∀ᵐ e ∂ν, IsFrame e)
    (hS : LinkStationary μ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    (∫ p, deriv φ (angle p.1 p.2) * defect p.1 p.2 ∂μ.prod ν) =
      ((n : ℝ)-2) * ∫ p, φ (angle p.1 p.2) * angle p.1 p.2 ∂μ.prod ν := by
  have hd := hφ.continuous_deriv (by simp)
  have h0 := stationary_product_integral hμ hν hS
    (fun f z ↦ φ (inner ℝ z f.1) • f.1)
    (fun f ↦ (hφ.comp (contDiff_id.inner ℝ contDiff_const)).smul contDiff_const)
    (fun p ↦ deriv φ (angle p.1 p.2) * defect p.1 p.2 -
      ((n : ℝ)-2) * (φ (angle p.1 p.2) * angle p.1 p.2))
    (((hd.comp continuous_angle).mul continuous_defect).sub
      (continuous_const.mul ((hφ.continuous.comp continuous_angle).mul continuous_angle)))
    (fun e f he hf ↦ by
      rw [linkDiv_scalar_constant he (hφ.differentiable (by simp))]
      ring)
  have hi1 : Integrable (fun p : Frame n × Frame n ↦ deriv φ (angle p.1 p.2) * defect p.1 p.2) (μ.prod ν) :=
    integrable_pairFrameFunction (product_frames hμ hν)
      ((hd.comp continuous_angle).mul continuous_defect)
  have hi2 : Integrable (fun p : Frame n × Frame n ↦ φ (angle p.1 p.2) * angle p.1 p.2) (μ.prod ν) :=
    integrable_pairFrameFunction (product_frames hμ hν)
      ((hφ.continuous.comp continuous_angle).mul continuous_angle)
  rw [integral_sub hi1 (hi2.const_mul ((n : ℝ)-2)), integral_const_mul] at h0
  exact sub_eq_zero.mp h0

lemma stationary_mixed_one {n : ℕ} {μ ν : Measure (Frame n)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ e ∂μ, IsFrame e) (hν : ∀ᵐ e ∂ν, IsFrame e)
    (hS : LinkStationary μ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    (∫ p, deriv φ (angle p.1 p.2) * cross p.1 p.2 ∂μ.prod ν) +
      (∫ p, φ (angle p.1 p.2) * traceProduct p.1 p.2 ∂μ.prod ν) -
      ((n : ℝ)-2) * ∫ p, φ (angle p.1 p.2) * defect p.2 p.1 ∂μ.prod ν = 0 := by
  have hd := hφ.continuous_deriv (by simp)
  have hswap : Continuous (fun p : Frame n × Frame n ↦ defect p.2 p.1) :=
    continuous_defect_reverse
  have hC : Continuous (fun p : Frame n × Frame n ↦ deriv φ (angle p.1 p.2) * cross p.1 p.2) :=
    (hd.comp continuous_angle).mul continuous_cross
  have hT : Continuous (fun p : Frame n × Frame n ↦ φ (angle p.1 p.2) * traceProduct p.1 p.2) :=
    (hφ.continuous.comp continuous_angle).mul continuous_traceProduct
  have hD : Continuous (fun p : Frame n × Frame n ↦ φ (angle p.1 p.2) * defect p.2 p.1) :=
    (hφ.continuous.comp continuous_angle).mul hswap
  have h0 := stationary_product_integral hμ hν hS
    (fun f z ↦ φ (inner ℝ z f.1) • projMap f z)
    (fun f ↦ (hφ.comp (contDiff_id.inner ℝ contDiff_const)).smul (projMap f).contDiff)
    (fun p ↦ deriv φ (angle p.1 p.2) * cross p.1 p.2 +
      φ (angle p.1 p.2) * traceProduct p.1 p.2 -
      ((n : ℝ)-2) * (φ (angle p.1 p.2) * defect p.2 p.1))
    ((hC.add hT).sub (continuous_const.mul hD))
    (fun e f he hf ↦ by
      rw [linkDiv_scalar_proj he hf (hφ.differentiable (by simp))]
      ring)
  have hiC := integrable_pairFrameFunction (product_frames hμ hν) hC
  have hiT := integrable_pairFrameFunction (product_frames hμ hν) hT
  have hiD := integrable_pairFrameFunction (product_frames hμ hν) hD
  have hiCT : Integrable (fun p : Frame n × Frame n ↦
      deriv φ (angle p.1 p.2) * cross p.1 p.2 +
      φ (angle p.1 p.2) * traceProduct p.1 p.2) (μ.prod ν) := hiC.add hiT
  rwa [integral_sub hiCT (hiD.const_mul ((n : ℝ)-2)), integral_add hiC hiT,
    integral_const_mul] at h0

lemma coupledStationarity_product {n : ℕ} {μ ν : Measure (Frame n)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ e ∂μ, IsFrame e) (hν : ∀ᵐ e ∂ν, IsFrame e)
    (hSμ : LinkStationary μ) (hSν : LinkStationary ν) : CoupledStationarity (μ.prod ν) := by
  constructor
  · intro φ hφ
    have hd := hφ.continuous_deriv (by simp)
    have hi1 : Integrable (fun p : Frame n × Frame n ↦ deriv φ (angle p.1 p.2) * defect p.1 p.2) (μ.prod ν) :=
      integrable_pairFrameFunction (product_frames hμ hν)
        ((hd.comp continuous_angle).mul continuous_defect)
    have hi2 : Integrable (fun p : Frame n × Frame n ↦ deriv φ (angle p.1 p.2) * defect p.2 p.1) (μ.prod ν) :=
      integrable_pairFrameFunction (product_frames hμ hν)
        ((hd.comp continuous_angle).mul (continuous_defect_reverse))
    have h1 := stationary_gradient_one hμ hν hSμ hφ
    have h2 := stationary_gradient_one hν hμ hSν hφ
    rw [← integral_prod_swap (fun p : Frame n × Frame n ↦ deriv φ (angle p.1 p.2) * defect p.1 p.2),
      ← integral_prod_swap (fun p : Frame n × Frame n ↦ φ (angle p.1 p.2) * angle p.1 p.2)] at h2
    simp only [Prod.fst_swap, Prod.snd_swap, angle_swap] at h2
    simp_rw [mul_add]
    rw [integral_add hi1 hi2, h1, h2]
    ring
  · intro φ hφ
    have h1 := stationary_mixed_one hμ hν hSμ hφ
    have h2 := stationary_mixed_one hν hμ hSν hφ
    rw [← integral_prod_swap (fun p : Frame n × Frame n ↦ deriv φ (angle p.1 p.2) * cross p.1 p.2),
      ← integral_prod_swap (fun p : Frame n × Frame n ↦ φ (angle p.1 p.2) * traceProduct p.1 p.2),
      ← integral_prod_swap (fun p : Frame n × Frame n ↦ φ (angle p.1 p.2) * defect p.2 p.1)] at h2
    simp only [Prod.fst_swap, Prod.snd_swap, angle_swap, cross_swap, traceProduct_swap] at h2
    have hi1 : Integrable (fun p : Frame n × Frame n ↦ φ (angle p.1 p.2) * defect p.1 p.2) (μ.prod ν) :=
      integrable_pairFrameFunction (product_frames hμ hν)
        ((hφ.continuous.comp continuous_angle).mul continuous_defect)
    have hi2 : Integrable (fun p : Frame n × Frame n ↦ φ (angle p.1 p.2) * defect p.2 p.1) (μ.prod ν) :=
      integrable_pairFrameFunction (product_frames hμ hν)
        ((hφ.continuous.comp continuous_angle).mul (continuous_defect_reverse))
    simp_rw [mul_add]
    rw [integral_add hi1 hi2]
    linarith

lemma minimizing_cones_coupledStationarity {n : ℕ} (hn : 1 < n) {E F : Set (Euc n)}
    (hE : IsLocallyPerimeterMinimizing E) (hF : IsLocallyPerimeterMinimizing F)
    (hcE : IsCone E) (hcF : IsCone F) :
    CoupledStationarity ((annularLink E).prod (annularLink F)) := by
  let := annularLink_finite hE
  let := annularLink_finite hF
  exact coupledStationarity_product (annularLink_frames hn hE hcE) (annularLink_frames hn hF hcF)
    (annularLink_stationary hn hE hcE) (annularLink_stationary hn hF hcF)

end SphericalFrankel
end RPISingularHarnack

end

end OAI
