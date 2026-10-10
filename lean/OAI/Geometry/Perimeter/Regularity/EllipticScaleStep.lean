import OAI.Geometry.Perimeter.Regularity.EllipticExcessStep
import OAI.Geometry.Perimeter.Regularity.EllipticRescale

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def scaledGradientEnergy (f : Euc n → ℝ) (p : Euc n) (r : ℝ) (q : Euc n) :=
  (r^n)⁻¹*gradientEnergy f p r q

theorem scaledGradientEnergy_nonneg (f : Euc n → ℝ) (p : Euc n) {r : ℝ} (hr : 0≤r) (q : Euc n) :
    0 ≤ scaledGradientEnergy f p r q :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hr _)) (integral_nonneg (fun _ ↦ sq_nonneg _))

theorem real_volume_ball_scale {r : ℝ} (hr : 0<r) :
    volume.real (Metric.ball (0:Euc n) r)=r^n*volume.real (Metric.ball (0:Euc n) 1) := by
  have h := integral_blownUpSet (E := Metric.ball (0:Euc n) (r*1)) measurableSet_ball (fun _ ↦ (1:ℝ)) 0 hr
  rw [blownUpSet_ball_self 0 hr 1] at h
  simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one] at h
  have hh := congrArg (fun a : ℝ ↦ r^n*a) h
  simpa only [←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hr.ne'),one_mul] using hh.symm

theorem linear_gradient_scaled_step (hn : 0<n) :
    ∃ C : ℝ, 0≤C ∧ ∀ (A : Euc n → Euc n →L[ℝ] Euc n), Continuous A →
      ∀ (f : Euc n → ℝ), ContDiff ℝ 1 f → ∀ (F : Euc n → Euc n), Continuous F →
      ∀ (p : Euc n) (r : ℝ), 0<r → WeakLinearEquation A f F (Metric.ball p r) →
      ∀ (A₀ : Euc n →L[ℝ] Euc n) (F₀ q : Euc n) (δ α β : ℝ),
      0≤δ → 0≤α → 0≤β →
      (∀ x∈Metric.ball p r, ‖ContinuousLinearMap.id ℝ (Euc n)-A x‖≤δ ∧
        ‖A₀-A x‖≤α ∧ ‖F x-F₀‖≤β) →
      ∃ q' : Euc n, ‖q'-q‖^2≤C^2*scaledGradientEnergy f p r q ∧
        ∀ θ : ℝ, 0<θ → θ≤1/2 → scaledGradientEnergy f p (θ*r) q' ≤
          (4*δ^2*(θ^n)⁻¹+2*C^2*θ^2*volume.real (Metric.ball (0:Euc n) 1))*scaledGradientEnergy f p r q+
          4*(α*‖q‖+β)^2*(θ^n)⁻¹*volume.real (Metric.ball (0:Euc n) 1) := by
  obtain ⟨C,hC,hB⟩ := linear_gradient_excess_step hn
  refine ⟨C,hC,fun A hA f hf F hF p r hr h A₀ F₀ q δ α β hδ hα hβ hb ↦ ?_⟩
  let a := fun x : Euc n ↦ A (p+r•x)
  let g := ellipticRescale f p r
  let B := fun x : Euc n ↦ F (p+r•x)
  have ha : Continuous a := hA.comp (continuous_const.add (continuous_id.const_smul r))
  have hg : ContDiff ℝ 1 g := ellipticRescale_contDiff hf p r
  have hB' : Continuous B := hF.comp (continuous_const.add (continuous_id.const_smul r))
  have hh : WeakLinearEquation a g B (Metric.ball 0 1) := by
    have hh := h.rescale (hf.differentiable (by simp)) p hr
    have hset : blownUpSet (Metric.ball p r) p r=Metric.ball (0:Euc n) 1 := by
      simpa only [mul_one] using blownUpSet_ball_self p hr 1
    rwa [hset] at hh
  have hb' : ∀ x∈Metric.ball (0:Euc n) 1, ‖ContinuousLinearMap.id ℝ (Euc n)-a x‖≤δ ∧
      ‖A₀-a x‖≤α ∧ ‖B x-F₀‖≤β := by
    intro x hx
    apply hb
    have hset := blownUpSet_ball_self p hr 1
    have hx' : x∈blownUpSet (Metric.ball p (r*1)) p r := by rw [hset]; exact hx
    simpa only [blownUpSet,mem_preimage,mul_one] using hx'
  obtain ⟨q',hq',hE⟩ := hB a ha g hg B hB' hh A₀ F₀ q δ α β hδ hα hβ hb'
  have hunit : gradientEnergy g 0 1 q=scaledGradientEnergy f p r q := by
    simpa only [mul_one,scaledGradientEnergy] using gradientEnergy_rescale (hf.differentiable (by simp)) p hr 1 q
  refine ⟨q',by simpa only [hunit] using hq',fun θ hθ hθ' ↦ ?_⟩
  have hi : scaledGradientEnergy f p (θ*r) q'=(θ^n)⁻¹*gradientEnergy g 0 θ q' := by
    rw [gradientEnergy_rescale (hf.differentiable (by simp)) p hr θ q']
    simp only [scaledGradientEnergy,mul_pow,mul_inv_rev,mul_comm θ r]
    ring
  rw [hi]
  have hnθ : θ^n≠0 := pow_ne_zero _ hθ.ne'
  have hbnd := mul_le_mul_of_nonneg_left (hE θ hθ') (inv_nonneg.mpr (pow_nonneg hθ.le n))
  rw [hunit,real_volume_ball_scale hθ] at hbnd
  convert hbnd using 1
  field_simp

end RPISingularHarnack

end

end OAI
