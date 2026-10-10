import Mathlib

namespace OAI

/-! Regular homogeneous functions, gradients, radial solutions and tube spaces. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes

variable (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W]

structure RegularHomogeneous where
  toFun : W → ℝ
  contDiff : ContDiff ℝ 1 toFun
  homogeneity : ∀ r : ℝ, 0 < r → ∀ w : W, toFun (r • w) = r ^ 2 * toFun w
  regular : ∀ w : W, w ≠ 0 → fderiv ℝ toFun w ≠ 0

namespace RegularHomogeneous

instance : CoeFun (RegularHomogeneous W) (fun _ => W → ℝ) := ⟨toFun⟩

variable {W}

def SmoothOffZero (f : RegularHomogeneous W) : Prop :=
  ContDiffOn ℝ ∞ f ({0}ᶜ : Set W)

@[ext] theorem ext {f g : RegularHomogeneous W} (h : ∀ w, f w = g w) : f = g := by
  cases f
  cases g
  simpa only [mk.injEq] using funext h

@[simp] theorem map_zero (f : RegularHomogeneous W) : f 0 = 0 := by
  have h := f.homogeneity 2 (by norm_num) 0
  simp only [smul_zero] at h
  nlinarith

theorem differentiable (f : RegularHomogeneous W) : Differentiable ℝ f :=
  f.contDiff.differentiable one_ne_zero

theorem euler (f : RegularHomogeneous W) (w : W) :
    fderiv ℝ f w w = 2 * f w := by
  have hl : HasDerivAt (fun t : ℝ => f (t • w)) (fderiv ℝ f w w) 1 := by
    convert! (f.differentiable ((id (1 : ℝ)) • w)).hasFDerivAt.comp_hasDerivAt 1
      ((hasDerivAt_id (1 : ℝ)).smul_const w) using 1; simp
  have hr : HasDerivAt (fun t : ℝ => t ^ 2 * f w) (2 * f w) 1 := by
    convert! ((hasDerivAt_id (1 : ℝ)).pow 2).mul_const (f w) using 1; norm_num
  have heq : (fun t : ℝ => f (t • w)) =ᶠ[𝓝 1] (fun t => t ^ 2 * f w) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact f.homogeneity t ht w
  exact (hl.congr_of_eventuallyEq heq.symm).unique hr

theorem fderiv_smul (f : RegularHomogeneous W) {r : ℝ} (hr : 0 < r) (w : W) :
    fderiv ℝ f (r • w) = r • fderiv ℝ f w := by
  have hd₁ : HasFDerivAt (fun x : W => f (r • x))
      ((fderiv ℝ f (r • w)).comp (r • ContinuousLinearMap.id ℝ W)) w :=
    (f.differentiable (r • w)).hasFDerivAt.comp w
      ((ContinuousLinearMap.id ℝ W).hasFDerivAt.const_smul r)
  have hd₂ : HasFDerivAt (fun x : W => r ^ 2 * f x)
      (r ^ 2 • fderiv ℝ f w) w := by
    convert! (f.differentiable w).hasFDerivAt.const_smul (r ^ 2) using 1
  have heq : (fun x : W => f (r • x)) = (fun x => r ^ 2 * f x) :=
    funext (f.homogeneity r hr)
  rw [heq] at hd₁
  have hlin := hd₁.unique hd₂
  ext u
  have hv := congrArg (fun A : W →L[ℝ] ℝ => A u) hlin
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at hv ⊢
  nlinarith [hr.ne']

def jet (f : RegularHomogeneous W) :
    C(Metric.sphere (0 : W) 1, ℝ) × C(Metric.sphere (0 : W) 1, W →L[ℝ] ℝ) :=
  (⟨fun u => f u, f.contDiff.continuous.comp continuous_subtype_val⟩,
   ⟨fun u => fderiv ℝ f u,
     (f.contDiff.continuous_fderiv one_ne_zero).comp continuous_subtype_val⟩)

instance : TopologicalSpace (RegularHomogeneous W) := TopologicalSpace.induced jet inferInstance

theorem jet_injective : Function.Injective (jet (W := W)) := by
  intro f g h
  ext w
  by_cases hw : w = 0
  · simp [hw]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let u : Metric.sphere (0 : W) 1 :=
    ⟨‖w‖⁻¹ • w, by
      simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_norm]
      exact inv_mul_cancel₀ hn.ne'⟩
  have hu : ‖w‖ • (u : W) = w := by
    simp only [u, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hv : f (u : W) = g (u : W) :=
    congrArg (fun p : C(Metric.sphere (0 : W) 1, ℝ) ×
      C(Metric.sphere (0 : W) 1, W →L[ℝ] ℝ) => p.1 u) h
  calc
    f w = ‖w‖ ^ 2 * f (u : W) := by rw [← f.homogeneity ‖w‖ hn, hu]
    _ = ‖w‖ ^ 2 * g (u : W) := by rw [hv]
    _ = g w := by rw [← g.homogeneity ‖w‖ hn, hu]

end RegularHomogeneous
end NearbyLagrangian.Tubes

namespace NearbyLagrangian.Tubes.RegularHomogeneous

open InnerProductSpace

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem gradient_smul (f : RegularHomogeneous W) {r : ℝ} (hr : 0 < r) (w : W) :
    gradient f (r • w) = r • gradient f w := by
  simp [gradient, f.fderiv_smul hr w]

@[simp] theorem gradient_zero (f : RegularHomogeneous W) : gradient f 0 = 0 := by
  have h := f.gradient_smul (r := 2) (by norm_num) 0
  simp only [smul_zero, two_smul] at h
  apply add_left_cancel (a := gradient f 0)
  simpa only [add_zero] using h.symm

theorem gradient_ne_zero (f : RegularHomogeneous W) {w : W} (hw : w ≠ 0) :
    gradient f w ≠ 0 := by
  intro h
  apply f.regular w hw
  rw [← toDual_gradient, h, _root_.map_zero]

theorem continuous_gradient (f : RegularHomogeneous W) : Continuous (gradient f) :=
  (toDual ℝ W).symm.continuous.comp (f.contDiff.continuous_fderiv one_ne_zero)

def direction (f : RegularHomogeneous W) (u : Metric.sphere (0 : W) 1) :
    Metric.sphere (0 : W) 1 :=
  ⟨‖gradient f u‖⁻¹ • gradient f u, by
    have hu : (u : W) ≠ 0 := by
      have := u.property
      simp only [Metric.mem_sphere, dist_zero_right] at this
      exact norm_ne_zero_iff.mp (by rw [this]; norm_num)
    have h := norm_pos_iff.mpr (f.gradient_ne_zero hu)
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm]
    exact inv_mul_cancel₀ h.ne'⟩

def radialSolution (f : RegularHomogeneous W) (R : ℝ)
    (u : Metric.sphere (0 : W) 1) : W := (R / ‖gradient f u‖) • (u : W)

theorem radialSolution_norm (f : RegularHomogeneous W) (R : ℝ) (hR : 0 < R)
    (u : Metric.sphere (0 : W) 1) :
    ‖f.radialSolution R u‖ = R / ‖gradient f u‖ := by
  have hu : ‖(u : W)‖ = 1 := by simp
  have hnonneg : 0 ≤ R / ‖gradient f u‖ := div_nonneg hR.le (norm_nonneg _)
  simp only [radialSolution, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg, hu,
    mul_one]

theorem radialSolution_critical (f : RegularHomogeneous W) (R : ℝ) (hR : 0 < R)
    (u : Metric.sphere (0 : W) 1) :
    gradient f (f.radialSolution R u) = R • (f.direction u : W) := by
  have hu : (u : W) ≠ 0 := by
    have : ‖(u : W)‖ = 1 := by simp
    exact norm_ne_zero_iff.mp (by rw [this]; norm_num)
  have hn : 0 < ‖gradient f u‖ := norm_pos_iff.mpr (f.gradient_ne_zero hu)
  rw [radialSolution, f.gradient_smul (div_pos hR hn)]
  simp only [direction, smul_smul, div_eq_mul_inv]

theorem radialSolution_ne_zero (f : RegularHomogeneous W) (R : ℝ) (hR : 0 < R)
    (u : Metric.sphere (0 : W) 1) : f.radialSolution R u ≠ 0 := by
  have hu : (u : W) ≠ 0 := by
    have : ‖(u : W)‖ = 1 := by simp
    exact norm_ne_zero_iff.mp (by rw [this]; norm_num)
  exact smul_ne_zero (div_ne_zero hR.ne' (norm_ne_zero_iff.mpr (f.gradient_ne_zero hu))) hu

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes.RegularHomogeneous

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def pullback (f : RegularHomogeneous V) (e : W ≃L[ℝ] V) : RegularHomogeneous W where
  toFun w := f (e w)
  contDiff := f.contDiff.comp e.contDiff
  homogeneity r hr w := by simpa only [map_smul] using f.homogeneity r hr (e w)
  regular w hw := by
    intro h
    have hd := (f.differentiable (e w)).hasFDerivAt.comp w e.hasFDerivAt
    have hcomp : (fderiv ℝ f (e w)).comp (e : W →L[ℝ] V) = 0 := hd.fderiv.symm.trans h
    apply f.regular (e w) (by simpa using hw)
    ext v
    have he := congrArg (fun A : W →L[ℝ] ℝ => A (e.symm v)) hcomp
    simpa using he

def directSum (f : RegularHomogeneous W) (g : RegularHomogeneous V) :
    RegularHomogeneous (W × V) where
  toFun w := f w.1 + g w.2
  contDiff := (f.contDiff.comp contDiff_fst).add (g.contDiff.comp contDiff_snd)
  homogeneity r hr w := by
    change f (r • w.1) + g (r • w.2) = _
    rw [f.homogeneity r hr, g.homogeneity r hr]
    ring
  regular w hw := by
    intro h
    have hd := ((f.differentiable w.1).hasFDerivAt.comp w
      (ContinuousLinearMap.fst ℝ W V).hasFDerivAt).add
      ((g.differentiable w.2).hasFDerivAt.comp w
      (ContinuousLinearMap.snd ℝ W V).hasFDerivAt)
    have hcomp := hd.fderiv.symm.trans h
    have hx : w.1 = 0 := by
      by_contra hne
      apply f.regular w.1 hne
      ext v
      have he := congrArg (fun A : W × V →L[ℝ] ℝ => A (v, 0)) hcomp
      simpa using he
    have hy : w.2 = 0 := by
      by_contra hne
      apply g.regular w.2 hne
      ext v
      have he := congrArg (fun A : W × V →L[ℝ] ℝ => A (0, v)) hcomp
      simpa using he
    exact hw (Prod.ext hx hy)

def neg (f : RegularHomogeneous W) : RegularHomogeneous W where
  toFun w := -f w
  contDiff := f.contDiff.neg
  homogeneity r hr w := by rw [f.homogeneity r hr]; ring
  regular w hw := by
    intro h
    apply f.regular w hw
    have hd := (f.differentiable w).hasFDerivAt.neg
    have hz := hd.fderiv.symm.trans h
    exact neg_eq_zero.mp hz

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes.RegularHomogeneous

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def positiveSquare : RegularHomogeneous W where
  toFun w := ‖w‖ ^ 2
  contDiff := contDiff_norm_sq ℝ
  homogeneity r hr w := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]; ring
  regular w hw := by
    intro h
    rw [fderiv_norm_sq_apply] at h
    have he := congrArg (fun A : W →L[ℝ] ℝ => A w) h
    simp only [two_smul, add_apply, innerSL_apply_apply,
      zero_apply, real_inner_self_eq_norm_sq] at he
    have := norm_pos_iff.mpr hw
    nlinarith [sq_pos_of_pos this]

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes

def standardForm (k l : ℕ) : RegularHomogeneous (EuclideanSpace ℝ (Fin (k + l))) :=
  RegularHomogeneous.pullback
    (RegularHomogeneous.directSum
      (RegularHomogeneous.neg (RegularHomogeneous.positiveSquare
        (W := EuclideanSpace ℝ (Fin k))))
      (RegularHomogeneous.positiveSquare (W := EuclideanSpace ℝ (Fin l))))
    EuclideanSpace.finAddEquivProd

def Tube (k l : ℕ) :=
  { f : RegularHomogeneous (EuclideanSpace ℝ (Fin (k + l))) //
    f ∈ pathComponent (standardForm k l) }

instance (k l : ℕ) : TopologicalSpace (Tube k l) := inferInstanceAs (TopologicalSpace
  { f : RegularHomogeneous (EuclideanSpace ℝ (Fin (k + l))) //
    f ∈ pathComponent (standardForm k l) })

def standardTube (k l : ℕ) : Tube k l :=
  ⟨standardForm k l, mem_pathComponent_self _⟩

end NearbyLagrangian.Tubes

end

end OAI
