import OAI.Geometry.Perimeter.Regularity.EllipticContinuousComparison

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def WeakLinearEquation (A : Euc n → Euc n →L[ℝ] Euc n) (f : Euc n → ℝ)
    (F : Euc n → Euc n) (U : Set (Euc n)) : Prop :=
  ∀ φ : SmoothLocalTest U,
    (∫ x, inner ℝ (A x (gradient f x)) (gradient φ.val x)) =
      ∫ x, inner ℝ (F x) (gradient φ.val x)

def linearResidual (A : Euc n → Euc n →L[ℝ] Euc n) (f : Euc n → ℝ)
    (F : Euc n → Euc n) (A₀ : Euc n →L[ℝ] Euc n) (F₀ q : Euc n) (x : Euc n) :=
  (gradient f x-q) - A x (gradient f x) + F x + (A₀ q-F₀)

theorem linearResidual_continuous {A : Euc n → Euc n →L[ℝ] Euc n}
    {f : Euc n → ℝ} {F : Euc n → Euc n} (hA : Continuous A) (hf : ContDiff ℝ 1 f)
    (hF : Continuous F) (A₀ : Euc n →L[ℝ] Euc n) (F₀ q : Euc n) :
    Continuous (linearResidual A f F A₀ F₀ q) :=
  ((((gradient_continuous_C1 hf).sub continuous_const).sub
    (hA.clm_apply (gradient_continuous_C1 hf))).add hF).add continuous_const

theorem linearResidual_pairing {A : Euc n → Euc n →L[ℝ] Euc n}
    {f : Euc n → ℝ} {F : Euc n → Euc n} {U : Set (Euc n)}
    (hA : Continuous A) (hf : ContDiff ℝ 1 f) (hF : Continuous F)
    (h : WeakLinearEquation A f F U) (A₀ : Euc n →L[ℝ] Euc n) (F₀ q : Euc n)
    (φ : SmoothLocalTest U) :
    (∫ x, inner ℝ (gradient (fun y ↦ f y-inner ℝ q y) x) (gradient φ.val x)) =
      ∫ x, inner ℝ (linearResidual A f F A₀ F₀ q x) (gradient φ.val x) := by
  have hg := inner_gradient_pairing_integrable (gradient_continuous_C1 hf) φ
  have hq := inner_gradient_pairing_integrable (continuous_const : Continuous (fun _ : Euc n ↦ q)) φ
  have hAf := inner_gradient_pairing_integrable (hA.clm_apply (gradient_continuous_C1 hf)) φ
  have hFi := inner_gradient_pairing_integrable hF φ
  have hc := inner_gradient_pairing_integrable
    (continuous_const : Continuous (fun _ : Euc n ↦ A₀ q-F₀)) φ
  simp_rw [gradient_sub_linear (hf.differentiable (by simp)),linearResidual,inner_add_left,inner_sub_left]
  simp_rw [← inner_sub_left (A₀ q) F₀]
  erw [integral_add ((hg.sub hq).sub hAf |>.add hFi) hc,
    integral_add ((hg.sub hq).sub hAf) hFi,integral_sub (hg.sub hq) hAf,
    constant_gradient_pairing_zero φ (A₀ q-F₀),h φ]
  ring_nf
  rfl

theorem linearResidual_bound {A : Euc n → Euc n →L[ℝ] Euc n}
    {f : Euc n → ℝ} {F : Euc n → Euc n} (A₀ : Euc n →L[ℝ] Euc n) (F₀ q x : Euc n)
    {δ α β : ℝ} (hδ : ‖ContinuousLinearMap.id ℝ (Euc n)-A x‖≤δ)
    (hα : ‖A₀-A x‖≤α) (hβ : ‖F x-F₀‖≤β) :
    ‖linearResidual A f F A₀ F₀ q x‖≤δ*‖gradient f x-q‖+α*‖q‖+β := by
  have he : linearResidual A f F A₀ F₀ q x =
      (ContinuousLinearMap.id ℝ (Euc n)-A x) (gradient f x-q)+(A₀-A x) q+(F x-F₀) := by
    simp only [linearResidual,sub_apply,ContinuousLinearMap.id_apply,map_sub]
    abel
  rw [he]
  have h1 := (ContinuousLinearMap.id ℝ (Euc n)-A x).le_opNorm (gradient f x-q)
  have h2 := (A₀-A x).le_opNorm q
  have hh := norm_add_le ((ContinuousLinearMap.id ℝ (Euc n)-A x) (gradient f x-q)+(A₀-A x) q) (F x-F₀)
  have hh' := norm_add_le ((ContinuousLinearMap.id ℝ (Euc n)-A x) (gradient f x-q)) ((A₀-A x) q)
  have h1' := mul_le_mul_of_nonneg_right hδ (norm_nonneg (gradient f x-q))
  have h2' := mul_le_mul_of_nonneg_right hα (norm_nonneg q)
  linarith

theorem continuous_residual_energy_bound {e W : Euc n → Euc n} (he : Continuous e)
    (hW : Continuous W) {δ b : ℝ} (hδ : 0≤δ) (hb : 0≤b)
    (h : ∀ x∈Metric.ball (0:Euc n) 1, ‖e x‖≤δ*‖W x‖+b) :
    (∫ x in Metric.ball (0:Euc n) 1, ‖e x‖^2) ≤
      2*δ^2*(∫ x in Metric.ball (0:Euc n) 1, ‖W x‖^2)+2*b^2*volume.real (Metric.ball (0:Euc n) 1) := by
  have hI (G : Euc n → Euc n) (hG : Continuous G) :
      IntegrableOn (fun x ↦ ‖G x‖^2) (Metric.ball (0:Euc n) 1) volume :=
    ((hG.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set Metric.ball_subset_closedBall
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0:Euc n) 1)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  calc
    _ ≤ ∫ x in Metric.ball (0:Euc n) 1, 2*δ^2*‖W x‖^2+2*b^2 := by
      apply integral_mono_ae (hI e he) (((hI W hW).const_mul _).add (integrable_const _))
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have hsq := (sq_le_sq₀ (norm_nonneg (e x))
        (add_nonneg (mul_nonneg hδ (norm_nonneg (W x))) hb)).2 (h x hx)
      change ‖e x‖^2≤2*δ^2*‖W x‖^2+2*b^2
      nlinarith [sq_nonneg (δ*‖W x‖-b)]
    _ = _ := by rw [integral_add ((hI W hW).const_mul _) (integrable_const _),integral_const_mul,integral_const]; simp [smul_eq_mul,mul_comm]

end RPISingularHarnack

end

end OAI
