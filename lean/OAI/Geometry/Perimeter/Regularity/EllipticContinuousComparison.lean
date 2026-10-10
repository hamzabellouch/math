import OAI.Geometry.Perimeter.Regularity.EllipticCutField

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def gradientEnergy (f : Euc n → ℝ) (p : Euc n) (r : ℝ) (q : Euc n) : ℝ :=
  ∫ x in Metric.ball p r, ‖gradient f x-q‖^2

theorem constant_gradient_pairing_zero {U : Set (Euc n)} (φ : SmoothLocalTest U) (q : Euc n) :
    (∫ x, inner ℝ q (gradient φ.val x))=0 := by
  have h := (scalar_compact_integration_parts_C1 (u := fun _ : Euc n ↦ (1:ℝ))
    contDiff_const (φ.property.1.of_le (by simp)) φ.property.2.1 q).2.2
  simpa [inner_gradient_right] using h

theorem inner_gradient_pairing_integrable {W : Euc n → Euc n} (hW : Continuous W)
    {U : Set (Euc n)} (φ : SmoothLocalTest U) :
    Integrable (fun x ↦ inner ℝ (W x) (gradient φ.val x)) volume :=
  (hW.inner (gradient_contDiff φ.property.1).continuous).integrable_of_hasCompactSupport
    ((gradient_hasCompactSupport φ.property.2.1).of_isClosed_subset (isClosed_tsupport _) (by
      apply closure_minimal _ (isClosed_tsupport _)
      intro x hx
      by_contra hh
      exact hx (by simp [image_eq_zero_of_notMem_tsupport hh])))

theorem gradient_sub_linear {f : Euc n → ℝ} (hf : Differentiable ℝ f) (q : Euc n) (x : Euc n) :
    gradient (fun y ↦ f y-inner ℝ q y) x=gradient f x-q := by
  apply ext_inner_right ℝ
  intro y
  simp only [inner_gradient_left,inner_sub_left]
  have h := ((hf x).hasFDerivAt.sub (innerSL ℝ q).hasFDerivAt).fderiv
  exact congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L y) h

theorem continuous_gradient_one_scale (hn : 0<n) :
    ∃ C : ℝ, 0≤C ∧ ∀ (f : Euc n → ℝ), ContDiff ℝ 1 f →
      ∀ (e : Euc n → Euc n), Continuous e →
      (∀ φ : SmoothLocalTest (Metric.ball 0 1),
        (∫ x, inner ℝ (gradient f x) (gradient φ.val x))=∫ x, inner ℝ (e x) (gradient φ.val x)) →
      ∃ q : Euc n, ‖q‖^2≤C^2*gradientEnergy f 0 1 0 ∧ ∀ θ : ℝ, θ≤1/2 →
        gradientEnergy f 0 θ q ≤ 2*(∫ x in Metric.ball 0 1, ‖e x‖^2)+
          2*C^2*gradientEnergy f 0 1 0*θ^2*volume.real (Metric.ball (0:Euc n) θ) := by
  obtain ⟨C,hC,hB⟩ := weak_field_one_scale hn
  refine ⟨C,hC,fun f hf e he h ↦ ?_⟩
  let u := cutFieldLp (gradient f) (gradient_continuous_C1 hf) 0 1
  let w := cutFieldLp e he 0 1
  have heq : ∀ φ : SmoothLocalTest (Metric.ball (0:Euc n) 1),
      (∫ x, inner ℝ (u x) (gradient φ.val x))=∫ x, inner ℝ (w x) (gradient φ.val x) := by
    intro φ
    rw [cutFieldLp_pairing _ _ _ _ ((tsupport_gradient_subset _).trans φ.property.2.2),
      cutFieldLp_pairing _ _ _ _ ((tsupport_gradient_subset _).trans φ.property.2.2)]
    exact h φ
  obtain ⟨q,hq,hqE⟩ := hB u w (cutGradient_curlFree hf 0 1) heq
  have huE : ‖u‖^2=gradientEnergy f 0 1 0 := by
    simpa only [gradientEnergy,sub_zero] using cutFieldLp_norm_sq (gradient f) (gradient_continuous_C1 hf) 0 1
  refine ⟨q,?_,fun θ hθ ↦ ?_⟩
  · calc
      ‖q‖^2 ≤ (C*‖u‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hq 2
      _ = C^2*gradientEnergy f 0 1 0 := by rw [mul_pow,huE]
  · have hE := hqE θ hθ
    have heU : (∫ x in Metric.ball 0 θ, ‖u x-q‖^2)=gradientEnergy f 0 θ q := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (cutFieldLp_ae (gradient f) (gradient_continuous_C1 hf) 0 1),
        ae_restrict_mem measurableSet_ball] with x hx hxB
      have hx1 : x∈Metric.ball (0:Euc n) 1 := Metric.ball_subset_ball (by linarith) hxB
      rw [hx,Set.indicator_of_mem hx1]
    rw [heU,cutFieldLp_norm_sq] at hE
    convert hE using 1
    rw [mul_pow,mul_pow,huE]
    ring

end RPISingularHarnack

end

end OAI
