import Mathlib
import OAI.Geometry.NearbyLagrangian.SmoothFamilies
import OAI.Geometry.NearbyLagrangian.FamilyApproximation

namespace OAI

/-! Homogeneous family blending and compact transverse tangent fields. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes.RegularHomogeneous
open scoped ContDiff Topology Manifold
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {B : Type*} [TopologicalSpace B]

theorem exists_family_blend (f : C(B,RegularHomogeneous E)) {g₀ : B → E → ℝ}
    (hg₀ : ∀ b, ContDiff ℝ 1 (g₀ b))
    (hh₀ : ∀ b (r:ℝ), 0 < r → ∀ x, g₀ b (r • x) = r^2 * g₀ b x)
    (hv₀ : Continuous (Function.uncurry g₀))
    (hd₀ : Continuous (fun p : B × E => fderiv ℝ (g₀ p.1) p.2))
    {c : ℝ} (hc : 0 < c)
    (hm : ∀ b x, ‖x‖ = 1 → c ≤ ‖fderiv ℝ (f b) x‖)
    (he : ∀ b x, ‖x‖ = 1 → ‖fderiv ℝ (g₀ b) x-fderiv ℝ (f b) x‖ < c) :
    ∃ g : C(B,RegularHomogeneous E), f.Homotopic g ∧ ∀ b x, g b x = g₀ b x := by
  let K : unitInterval × B → RegularHomogeneous E := fun p =>
    controlledBlend (f p.2) (hg₀ p.2) (hh₀ p.2) hc (hm p.2) (he p.2) p.1
  have hvf : Continuous (fun p : B × E => f p.1 p.2) :=
    continuous_eval.comp (f.continuous.prodMap continuous_id)
  have hdf : Continuous (fun p : B × E => fderiv ℝ (f p.1) p.2) :=
    continuous_fderiv_eval.comp (f.continuous.prodMap continuous_id)
  have hK : Continuous K := by
    apply continuous_of_joint_jet
    · change Continuous (fun p : (unitInterval × B) × Metric.sphere (0:E) 1 =>
        f p.1.2 p.2 + (p.1.1 : ℝ) * (g₀ p.1.2 p.2 - f p.1.2 p.2))
      have hcoord : Continuous (fun p : (unitInterval × B) × Metric.sphere (0:E) 1 =>
          (p.1.2, (p.2 : E))) :=
        (continuous_snd.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)
      exact (hvf.comp hcoord).add
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul
          ((hv₀.comp hcoord).sub (hvf.comp hcoord)))
    · change Continuous (fun p : (unitInterval × B) × Metric.sphere (0:E) 1 =>
        fderiv ℝ (fun w => f p.1.2 w + (p.1.1 : ℝ) * (g₀ p.1.2 w - f p.1.2 w)) p.2)
      simp only [fderiv_blend _ (hg₀ _)]
      have hcoord : Continuous (fun p : (unitInterval × B) × Metric.sphere (0:E) 1 =>
          (p.1.2, (p.2 : E))) :=
        (continuous_snd.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)
      exact (hdf.comp hcoord).add
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).smul
          ((hd₀.comp hcoord).sub (hdf.comp hcoord)))
  let g : C(B,RegularHomogeneous E) :=
    ⟨fun b => K (1,b), hK.comp (continuous_const.prodMk continuous_id)⟩
  have hH : f.Homotopic g := by
    exact ⟨{ toFun := K
             continuous_toFun := hK
             map_zero_left := fun _ => controlledBlend_zero _ _ _ _ _ _
             map_one_left := fun _ => rfl }⟩
  refine ⟨g,hH,?_⟩
  intro b x
  exact controlledBlend_one_apply (f b) (hg₀ b) (hh₀ b) hc (hm b) (he b) x

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  [ChartedSpace H B] [IsManifold I ∞ B] [T2Space B] [CompactSpace B]

theorem exists_smooth_homotopic_close_on_sphere (f : C(B,RegularHomogeneous E))
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hεc : ε < c)
    (hm : ∀ b x, ‖x‖ = 1 → c ≤ ‖fderiv ℝ (f b) x‖) :
    ∃ g : C(B,RegularHomogeneous E), f.Homotopic g ∧
      (∀ p : B × E, p.2 ≠ 0 →
        ContMDiffAt (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ (fun p => g p.1 p.2) p) ∧
      ∀ b x, ‖x‖ = 1 → |g b x-f b x| ≤ ε ∧
        ‖fderiv ℝ (g b) x-fderiv ℝ (f b) x‖ ≤ ε := by
  obtain ⟨g₀,hg₀,_,hh₀,hs₀,hv₀,hd₀,he₀⟩ := exists_smooth_family_approx (I:=I) f.continuous hε
  obtain ⟨g,hH,hg⟩ := exists_family_blend f hg₀ hh₀ hv₀ hd₀ hc hm
    (fun b x hx => ((he₀ b x hx).2).trans_lt hεc)
  have heq (b : B) : (g b : E → ℝ) = g₀ b := funext (hg b)
  refine ⟨g,hH,?_,?_⟩
  · have heq' : (fun p : B × E => g p.1 p.2) = Function.uncurry g₀ :=
      funext (fun p => hg p.1 p.2)
    rw [heq']
    exact hs₀
  · intro b x hx
    rw [hg b x,heq b]
    simpa only [Real.norm_eq_abs] using he₀ b x hx

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes.RegularHomogeneous
open Set Filter Metric
open scoped Topology InnerProductSpace ContDiff
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

def tangentGradient (f : RegularHomogeneous W) (w : W) : W :=
  ‖w‖ ^ 2 • gradient f w - (2*f w) • w

lemma inner_tangentGradient (f : RegularHomogeneous W) (w : W) :
    ⟪w,f.tangentGradient w⟫_ℝ = 0 := by
  rw [tangentGradient, inner_sub_right, real_inner_smul_right,
    real_inner_smul_right, ← real_inner_comm w (gradient f w),
    inner_gradient_left, f.euler, real_inner_self_eq_norm_sq]
  ring

lemma fderiv_tangentGradient (f : RegularHomogeneous W) (w : W) :
    fderiv ℝ f w (f.tangentGradient w) = ‖w‖^2 * ‖gradient f w‖^2 - 4*(f w)^2 := by
  rw [← inner_gradient_left, tangentGradient, inner_sub_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    inner_gradient_left, f.euler]
  ring

lemma tangentGradient_norm_sq (f : RegularHomogeneous W) (w : W) :
    ‖f.tangentGradient w‖^2 = ‖w‖^2 * fderiv ℝ f w (f.tangentGradient w) := by
  rw [← real_inner_self_eq_norm_sq, tangentGradient, inner_sub_left,
    real_inner_smul_left, real_inner_smul_left]
  change ‖w‖^2 * ⟪gradient f w,f.tangentGradient w⟫_ℝ -
    (2*f w) * ⟪w,f.tangentGradient w⟫_ℝ = _
  rw [inner_tangentGradient, mul_zero, sub_zero, inner_gradient_left]
  rfl

lemma tangentGradient_on_sphere (f : RegularHomogeneous W) {w : W} (hw : ‖w‖ = 1) :
    fderiv ℝ f w (f.tangentGradient w) = ‖f.tangentGradient w‖^2 := by
  simpa only [hw, one_pow, one_mul] using (f.tangentGradient_norm_sq w).symm

lemma contDiffAt_tangentGradient {f : RegularHomogeneous W} (hf : f.SmoothOffZero)
    {w : W} (hw : w ≠ 0) : ContDiffAt ℝ ∞ f.tangentGradient w := by
  have hfw : ContDiffAt ℝ ∞ f w :=
    hf.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hw))
  exact ((contDiffAt_id.norm_sq ℝ).smul (f.contDiffAt_gradient hf hw)).sub
    ((contDiffAt_const.mul hfw).smul contDiffAt_id)

lemma tangentGradient_band [ProperSpace W] [Nontrivial W] (f : RegularHomogeneous W) :
    ∃ c > 0, ∀ w, ‖w‖ = 1 → |f w| < c/4 →
       c^2/2 < ‖f.tangentGradient w‖^2 := by
  obtain ⟨c,C,hc,_,hbound⟩ := f.gradient_bounds
  refine ⟨c,hc,?_⟩
  intro w hw hf
  have hg : c ≤ ‖gradient f w‖ := by simpa only [hw,mul_one] using (hbound w).1
  have hq : ‖f.tangentGradient w‖^2 = ‖gradient f w‖^2 - 4*(f w)^2 := by
    rw [← f.tangentGradient_on_sphere hw, f.fderiv_tangentGradient, hw, one_pow, one_mul]
  have habs : (f w)^2 < (c/4)^2 := by
    nlinarith [sq_abs (f w), abs_nonneg (f w)]
  nlinarith [sq_nonneg (‖gradient f w‖-c)]

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes.RegularHomogeneous
open Set Filter Metric
open scoped Topology InnerProductSpace ContDiff
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Nontrivial W]

theorem exists_compact_tangent_field (f : RegularHomogeneous W) (hf : f.SmoothOffZero) :
    ∃ R > 0, ∃ F : W → W, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      (∀ w, ⟪w,F w⟫_ℝ = 0) ∧
      (∀ w, ‖w‖ = 1 → fderiv ℝ f w (F w) ∈ Icc (0:ℝ) 1) ∧
      (∀ w, ‖w‖ = 1 → |f w| < R → fderiv ℝ f w (F w) = 1) := by
  obtain ⟨c,hc,hband⟩ := f.tangentGradient_band
  let η : ContDiffBump (0:ℝ) := ⟨c^2/4,c^2/2,by positivity,by nlinarith [sq_pos_of_pos hc]⟩
  let outer : ContDiffBump (0:W) := ⟨2,3,by norm_num,by norm_num⟩
  let inner : ContDiffBump (0:W) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  let ψ : W → ℝ := fun w => outer w * (1-inner w)
  let q : W → ℝ := fun w => ‖f.tangentGradient w‖^2
  let d : W → ℝ := fun w => q w + η (q w)
  let F : W → W := fun w => (ψ w / d w) • f.tangentGradient w
  have hq (w : W) : 0 ≤ q w := sq_nonneg _
  have hd (w : W) : 0 < d w := by
    by_cases h : q w = 0
    · have hη : η (0:ℝ) = 1 := η.one_of_mem_closedBall (by
        rw [mem_closedBall, dist_self]; exact η.rIn_pos.le)
      simp only [d,h,hη,zero_add,zero_lt_one]
    · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hq w) (Ne.symm h)) η.nonneg
  have hψ (w : W) : ψ w ∈ Icc (0:ℝ) 1 := by
    dsimp [ψ]
    constructor
    · exact mul_nonneg outer.nonneg (sub_nonneg.mpr inner.le_one)
    · nlinarith [outer.nonneg (x := w), outer.le_one (x := w),
        inner.nonneg (x := w), inner.le_one (x := w)]
  have hψsphere (w : W) (hw : ‖w‖ = 1) : ψ w = 1 := by
    have ho : outer w = 1 := outer.one_of_mem_closedBall (by
      simpa only [mem_closedBall, dist_zero_right, hw, outer] using (show (1:ℝ) ≤ 2 by norm_num))
    have hi : inner w = 0 := inner.zero_of_le_dist (by
      simpa only [dist_zero_right, hw, inner] using (show (1:ℝ)/2 ≤ 1 by norm_num))
    simp only [ψ,ho,hi,sub_zero,mul_one]
  have hFs : ContDiff ℝ ∞ F := by
    rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hw : w = 0
    · subst w
      apply (contDiffAt_const (c := (0:W))).congr_of_eventuallyEq
      filter_upwards [inner.eventuallyEq_one_of_mem_ball (show (0:W) ∈ ball 0 inner.rIn by
        rw [mem_ball, dist_self]; exact inner.rIn_pos)] with w hw
      change inner w = 1 at hw
      simp only [F,ψ,hw,sub_self,mul_zero,zero_div,zero_smul]
    · have hT := f.contDiffAt_tangentGradient hf hw
      have hq' : ContDiffAt ℝ ∞ q w := hT.norm_sq ℝ
      have hd' : ContDiffAt ℝ ∞ d w := hq'.add (η.contDiffAt.comp w hq')
      exact (((outer.contDiffAt.mul (contDiffAt_const.sub inner.contDiffAt)).div hd'
        (hd w).ne').smul hT)
  have hFc : HasCompactSupport F := by
    have hp : HasCompactSupport ψ := outer.hasCompactSupport.mul_right
    have hp' : HasCompactSupport (fun w => ψ w * (d w)⁻¹) := hp.mul_right
    change HasCompactSupport ((fun w => ψ w * (d w)⁻¹) • f.tangentGradient)
    exact hp'.smul_right
  refine ⟨c/4,by positivity,F,hFs,hFc,?_,?_,?_⟩
  · intro w
    simp only [F,real_inner_smul_right,f.inner_tangentGradient,mul_zero]
  · intro w hw
    have he : fderiv ℝ f w (F w) = ψ w * (q w / d w) := by
      simp only [F,map_smul,smul_eq_mul,f.tangentGradient_on_sphere hw,q]
      ring
    rw [he]
    have hdq : q w ≤ d w := le_add_of_nonneg_right η.nonneg
    have hratio : q w / d w ∈ Icc (0:ℝ) 1 :=
      ⟨div_nonneg (hq w) (hd w).le, (div_le_one (hd w)).mpr hdq⟩
    constructor
    · exact mul_nonneg (hψ w).1 hratio.1
    · nlinarith [(hψ w).1,(hψ w).2,hratio.1,hratio.2]
  · intro w hw hfw
    have hη : η (q w) = 0 := η.zero_of_le_dist (by
      simp only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (hq w)]
      exact (hband w hw hfw).le)
    have hdz : d w = q w := by simp only [d,hη,add_zero]
    have hqz : q w ≠ 0 := by rw [← hdz]; exact (hd w).ne'
    simp only [F,map_smul,smul_eq_mul,f.tangentGradient_on_sphere hw,
      hψsphere w hw,hdz,q] at *
    exact one_div_mul_cancel hqz

end NearbyLagrangian.Tubes.RegularHomogeneous

end

end OAI
