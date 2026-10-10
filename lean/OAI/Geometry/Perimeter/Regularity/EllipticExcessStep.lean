import OAI.Geometry.Perimeter.Regularity.EllipticLinearStep

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem linear_gradient_excess_step (hn : 0<n) :
    ∃ C : ℝ, 0≤C ∧ ∀ (A : Euc n → Euc n →L[ℝ] Euc n), Continuous A →
      ∀ (f : Euc n → ℝ), ContDiff ℝ 1 f → ∀ (F : Euc n → Euc n), Continuous F →
      WeakLinearEquation A f F (Metric.ball 0 1) →
      ∀ (A₀ : Euc n →L[ℝ] Euc n) (F₀ q : Euc n) (δ α β : ℝ),
      0≤δ → 0≤α → 0≤β →
      (∀ x∈Metric.ball (0:Euc n) 1, ‖ContinuousLinearMap.id ℝ (Euc n)-A x‖≤δ ∧
        ‖A₀-A x‖≤α ∧ ‖F x-F₀‖≤β) →
      ∃ q' : Euc n, ‖q'-q‖^2≤C^2*gradientEnergy f 0 1 q ∧
        ∀ θ : ℝ, θ≤1/2 → gradientEnergy f 0 θ q' ≤
          (4*δ^2+2*C^2*θ^2*volume.real (Metric.ball (0:Euc n) θ))*gradientEnergy f 0 1 q+
          4*(α*‖q‖+β)^2*volume.real (Metric.ball (0:Euc n) 1) := by
  obtain ⟨C,hC,hB⟩ := continuous_gradient_one_scale hn
  refine ⟨C,hC,fun A hA f hf F hF h A₀ F₀ q δ α β hδ hα hβ hb ↦ ?_⟩
  let g : Euc n → ℝ := fun x ↦ f x-inner ℝ q x
  have hg : ContDiff ℝ 1 g := hf.sub (innerSL ℝ q).contDiff
  let e := linearResidual A f F A₀ F₀ q
  have he : Continuous e := linearResidual_continuous hA hf hF _ _ _
  obtain ⟨z,hz,hzE⟩ := hB g hg e he (linearResidual_pairing hA hf hF h A₀ F₀ q)
  have hgrad (x : Euc n) : gradient g x=gradient f x-q := gradient_sub_linear (hf.differentiable (by simp)) q x
  have hE (r : ℝ) (w : Euc n) : gradientEnergy g 0 r w=gradientEnergy f 0 r (q+w) := by
    unfold gradientEnergy
    simp_rw [hgrad,sub_sub]
  have hBnd := continuous_residual_energy_bound he ((gradient_continuous_C1 hf).sub continuous_const)
    hδ (add_nonneg (mul_nonneg hα (norm_nonneg _)) hβ) (fun x hx ↦ by
      have hx' := hb x hx
      simpa only [add_assoc,Pi.sub_apply,e] using linearResidual_bound (f := f) A₀ F₀ q x hx'.1 hx'.2.1 hx'.2.2)
  change (∫ x in Metric.ball (0:Euc n) 1, ‖e x‖^2)≤
    2*δ^2*gradientEnergy f 0 1 q+2*(α*‖q‖+β)^2*volume.real (Metric.ball (0:Euc n) 1) at hBnd
  refine ⟨q+z,?_,fun θ hθ ↦ ?_⟩
  · simpa only [add_sub_cancel_left,hE,add_zero] using hz
  · have hh := hzE θ hθ
    rw [hE,hE,add_zero] at hh
    nlinarith

end RPISingularHarnack

end

end OAI
