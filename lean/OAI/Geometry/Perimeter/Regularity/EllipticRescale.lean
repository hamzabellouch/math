import OAI.Geometry.Perimeter.Regularity.EllipticLinearStep

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def ellipticRescale (f : Euc n → ℝ) (p : Euc n) (r : ℝ) (x : Euc n) := r⁻¹*f (p+r•x)

theorem ellipticRescale_contDiff {f : Euc n → ℝ} {k : ℕ∞} (hf : ContDiff ℝ k f)
    (p : Euc n) (r : ℝ) : ContDiff ℝ k (ellipticRescale f p r) :=
  contDiff_const.mul (hf.comp (contDiff_const.add (contDiff_id.const_smul r)))

theorem ellipticRescale_gradient {f : Euc n → ℝ} (hf : Differentiable ℝ f)
    (p : Euc n) {r : ℝ} (hr : r≠0) (x : Euc n) :
    gradient (ellipticRescale f p r) x=gradient f (p+r•x) := by
  apply ext_inner_right ℝ
  intro y
  simp only [inner_gradient_left]
  have h := ((((hf (p+r•x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul r |>.const_add p))).const_mul r⁻¹).fderiv
  have he := congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L y) h
  change fderiv ℝ (fun y ↦ r⁻¹*f (p+r•y)) x y = _
  simpa [ContinuousLinearMap.comp_apply,hr,mul_assoc] using he

theorem integral_affine (g : Euc n → ℝ) (p : Euc n) {r : ℝ} (hr : 0<r) :
    (∫ x, g (p+r•x))=(r^n)⁻¹*∫ x, g x := by
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure (Euc n))
    (fun x ↦ g (p+x)) r (hR := hr.le)
  simpa only [finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul,integral_add_left_eq_self] using h

theorem blownUpSet_ball_self (p : Euc n) {r : ℝ} (hr : 0<r) (R : ℝ) :
    blownUpSet (Metric.ball p (r*R)) p r=Metric.ball (0:Euc n) R := by
  ext x
  simp only [blownUpSet,mem_preimage,Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,
    norm_smul,Real.norm_of_nonneg hr.le,sub_zero]
  exact mul_lt_mul_iff_right₀ hr

theorem gradientEnergy_rescale {f : Euc n → ℝ} (hf : Differentiable ℝ f)
    (p : Euc n) {r : ℝ} (hr : 0<r) (R : ℝ) (q : Euc n) :
    gradientEnergy (ellipticRescale f p r) 0 R q=(r^n)⁻¹*gradientEnergy f p (r*R) q := by
  unfold gradientEnergy
  simp_rw [ellipticRescale_gradient hf p hr.ne']
  rw [←blownUpSet_ball_self p hr R]
  exact integral_blownUpSet (E := Metric.ball p (r*R)) measurableSet_ball (fun x ↦ ‖gradient f x-q‖^2) p hr

def affineLocalTest {U : Set (Euc n)} (p : Euc n) {r : ℝ} (hr : 0<r)
    (φ : SmoothLocalTest (blownUpSet U p r)) : SmoothLocalTest U := by
  let ψ : Euc n → ℝ := fun y ↦ r*φ.val (r⁻¹•(y-p))
  refine ⟨ψ,?_,?_,?_⟩
  · exact contDiff_const.mul (φ.property.1.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹))
  · exact (φ.property.2.1.comp_homeomorph
      ((Homeomorph.subRight p).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')))).mul_left
  · have hs : tsupport ψ ⊆ tsupport (fun y ↦ φ.val (r⁻¹•(y-p))) := tsupport_mul_subset_right
    intro y hy
    have hh := φ.property.2.2 (tsupport_comp_subset_preimage φ.val
      ((continuous_id.sub continuous_const).const_smul r⁻¹) (hs hy))
    simpa only [blownUpSet,mem_preimage,Pi.smul_apply,Pi.sub_apply,id_eq,smul_inv_smul₀ hr.ne',add_sub_cancel] using hh

theorem affineLocalTest_gradient {U : Set (Euc n)} (p : Euc n) {r : ℝ} (hr : 0<r)
    (φ : SmoothLocalTest (blownUpSet U p r)) (x : Euc n) :
    gradient (affineLocalTest p hr φ).val (p+r•x)=gradient φ.val x := by
  have hh := ellipticRescale_gradient (φ.property.1.differentiable (by simp))
    (-(r⁻¹•p)) (inv_ne_zero hr.ne') (p+r•x)
  have he : (affineLocalTest p hr φ).val=ellipticRescale φ.val (-(r⁻¹•p)) r⁻¹ := by
    funext y
    simp only [affineLocalTest,ellipticRescale,inv_inv,sub_eq_add_neg,smul_add,smul_neg,add_comm]
  rw [he,hh]
  congr 1
  simp [smul_add,inv_smul_smul₀ hr.ne',add_comm]

theorem WeakLinearEquation.rescale {A : Euc n → Euc n →L[ℝ] Euc n}
    {f : Euc n → ℝ} {F : Euc n → Euc n} {U : Set (Euc n)}
    (h : WeakLinearEquation A f F U) (hf : Differentiable ℝ f)
    (p : Euc n) {r : ℝ} (hr : 0<r) :
    WeakLinearEquation (fun x ↦ A (p+r•x)) (ellipticRescale f p r)
      (fun x ↦ F (p+r•x)) (blownUpSet U p r) := by
  intro φ
  have he := h (affineLocalTest p hr φ)
  have h1 := integral_affine (fun y ↦ inner ℝ (A y (gradient f y))
    (gradient (affineLocalTest p hr φ).val y)) p hr
  have h2 := integral_affine (fun y ↦ inner ℝ (F y)
    (gradient (affineLocalTest p hr φ).val y)) p hr
  simp_rw [affineLocalTest_gradient p hr φ] at h1 h2
  simp_rw [ellipticRescale_gradient hf p hr.ne']
  rw [h1,h2,he]

end RPISingularHarnack

end

end OAI
