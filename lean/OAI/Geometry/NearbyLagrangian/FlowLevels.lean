import Mathlib
import OAI.Geometry.NearbyLagrangian.CompleteFlow
import OAI.Geometry.NearbyLagrangian.SphereFields

namespace OAI

/-! Flow collars, level translation and homotopy equivalences of negative sets. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.ODE.CompleteFlow
open Set Filter Metric
open scoped Topology NNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : E → E} (φ : CompleteFlow F)

theorem observable_lipschitz {f : E → ℝ} (hf : Differentiable ℝ f)
    {C : ℝ≥0} (hC : ∀ x, ‖fderiv ℝ f x (F x)‖ ≤ C) (x : E) :
    LipschitzWith C (fun t => f (φ.toFun (x,t))) := by
  have hd (t : ℝ) := (hf (φ.toFun (x,t))).hasFDerivAt.comp_hasDerivAt t
    (φ.derivative x t)
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hd t).differentiableAt)
  intro t
  rw [(hd t).deriv]
  exact_mod_cast hC (φ.toFun (x,t))

theorem translate_level {f : E → ℝ} (hf : Differentiable ℝ f)
    (hC : ∀ x, ‖fderiv ℝ f x (F x)‖ ≤ 1) {R : ℝ}
    (hR : ∀ x, |f x| < R → fderiv ℝ f x (F x) = 1)
    {x : E} {t : ℝ} (ht : |f x| + |t| < R) :
    f (φ.toFun (x,t)) = f x + t := by
  let r := R - |f x|
  have hr : 0 < r := by dsimp [r]; linarith [abs_nonneg t]
  have hL := φ.observable_lipschitz hf (C := 1) hC x
  have hstay {s : ℝ} (hs : s ∈ Ioo (-r) r) : |f (φ.toFun (x,s))| < R := by
    have hs' : |s| < r := abs_lt.mpr hs
    have h : |f (φ.toFun (x,s)) - f x| ≤ |s| := by
      simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul,
        sub_zero, φ.initial] using hL.dist_le_mul s 0
    calc |f (φ.toFun (x,s))| ≤ |f (φ.toFun (x,s)) - f x| + |f x| := by
           simpa only [sub_add_cancel] using abs_add_le (f (φ.toFun (x,s))-f x) (f x)
         _ ≤ |s| + |f x| := by linarith
         _ < R := by dsimp [r] at hs'; linarith
  have hd {s : ℝ} (hs : s ∈ Ioo (-r) r) :
      HasDerivAt (fun s => f (φ.toFun (x,s))) 1 s := by
    simpa only [Function.comp_def, hR _ (hstay hs)] using
      (hf (φ.toFun (x,s))).hasFDerivAt.comp_hasDerivAt s (φ.derivative x s)
  have hd' (s : ℝ) : HasDerivAt (fun s => f x+s) 1 s :=
    (hasDerivAt_id s).const_add (f x)
  have heq := isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (-r) r).isPreconnected
    (fun s hs => (hd hs).differentiableAt.differentiableWithinAt)
    (fun s _ => (hd' s).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd hs).deriv.trans (hd' s).deriv.symm)
    (show (0:ℝ) ∈ Ioo (-r) r from ⟨by linarith,hr⟩)
    (show f (φ.toFun (x,0)) = f x+0 by rw [φ.initial, add_zero])
  apply heq
  apply abs_lt.mp
  dsimp [r]
  linarith

end NearbyLagrangian.ODE.CompleteFlow

namespace NearbyLagrangian.ODE.CompleteFlow
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : E → E} (φ : CompleteFlow F)

theorem norm_eq (hF : ∀ x, ⟪x,F x⟫_ℝ = 0) (x : E) (t : ℝ) :
    ‖φ.toFun (x,t)‖ = ‖x‖ := by
  have hd (s : ℝ) : HasDerivAt (fun s => ‖φ.toFun (x,s)‖ ^ 2) 0 s := by
    simpa only [hF, mul_zero] using (φ.derivative x s).norm_sq
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  rw [φ.initial] at he
  nlinarith [norm_nonneg (φ.toFun (x,t)), norm_nonneg x]

end NearbyLagrangian.ODE.CompleteFlow

namespace NearbyLagrangian.ODE.CompleteFlow
open Set Filter Metric
open scoped Topology NNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : E → E} (φ : CompleteFlow F)

theorem observable_lipschitz_on {f : E → ℝ} (hf : Differentiable ℝ f)
    {C : ℝ≥0} (x : E) (hC : ∀ t, ‖fderiv ℝ f (φ.toFun (x,t)) (F (φ.toFun (x,t)))‖ ≤ C) :
    LipschitzWith C (fun t => f (φ.toFun (x,t))) := by
  have hd (t : ℝ) := (hf (φ.toFun (x,t))).hasFDerivAt.comp_hasDerivAt t
    (φ.derivative x t)
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hd t).differentiableAt)
  intro t
  rw [(hd t).deriv]
  exact_mod_cast hC t

theorem translate_level_on {f : E → ℝ} (hf : Differentiable ℝ f)
    {S : Set E} (hS : ∀ x ∈ S, ∀ t, φ.toFun (x,t) ∈ S)
    (hC : ∀ x ∈ S, ‖fderiv ℝ f x (F x)‖ ≤ 1) {R : ℝ}
    (hR : ∀ x ∈ S, |f x| < R → fderiv ℝ f x (F x) = 1)
    {x : E} (hx : x ∈ S) {t : ℝ} (ht : |f x| + |t| < R) :
    f (φ.toFun (x,t)) = f x + t := by
  let r := R - |f x|
  have hr : 0 < r := by dsimp [r]; linarith [abs_nonneg t]
  have hL := φ.observable_lipschitz_on hf (C := 1) x (fun t => hC _ (hS x hx t))
  have hstay {s : ℝ} (hs : s ∈ Ioo (-r) r) : |f (φ.toFun (x,s))| < R := by
    have hs' : |s| < r := abs_lt.mpr hs
    have h : |f (φ.toFun (x,s)) - f x| ≤ |s| := by
      simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul,
        sub_zero, φ.initial] using hL.dist_le_mul s 0
    calc |f (φ.toFun (x,s))| ≤ |f (φ.toFun (x,s)) - f x| + |f x| := by
           simpa only [sub_add_cancel] using abs_add_le (f (φ.toFun (x,s))-f x) (f x)
         _ ≤ |s| + |f x| := by linarith
         _ < R := by dsimp [r] at hs'; linarith
  have hd {s : ℝ} (hs : s ∈ Ioo (-r) r) :
      HasDerivAt (fun s => f (φ.toFun (x,s))) 1 s := by
    simpa only [Function.comp_def, hR _ (hS x hx s) (hstay hs)] using
      (hf (φ.toFun (x,s))).hasFDerivAt.comp_hasDerivAt s (φ.derivative x s)
  have hd' (s : ℝ) : HasDerivAt (fun s => f x+s) 1 s :=
    (hasDerivAt_id s).const_add (f x)
  have heq := isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (-r) r).isPreconnected
    (fun s hs => (hd hs).differentiableAt.differentiableWithinAt)
    (fun s _ => (hd' s).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd hs).deriv.trans (hd' s).deriv.symm)
    (show (0:ℝ) ∈ Ioo (-r) r from ⟨by linarith,hr⟩)
    (show f (φ.toFun (x,0)) = f x+0 by rw [φ.initial, add_zero])
  apply heq
  apply abs_lt.mp
  dsimp [r]
  linarith

end NearbyLagrangian.ODE.CompleteFlow

namespace NearbyLagrangian.ODE.CompleteFlow
open Set Filter Metric
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : E → E} (φ : CompleteFlow F)

def levelCollarOn {K : ℝ≥0} (hK : LipschitzWith K F)
    {f : E → ℝ} (hf : Differentiable ℝ f)
    {S : Set E} (hS : ∀ x ∈ S, ∀ t, φ.toFun (x,t) ∈ S)
    (hC : ∀ x ∈ S, ‖fderiv ℝ f x (F x)‖ ≤ 1) {R r : ℝ} (hr : 0 < r)
    (h2 : 2*r ≤ R) (hR : ∀ x ∈ S, |f x| < R → fderiv ℝ f x (F x) = 1) :
    ({x : E // x ∈ S ∧ f x = 0} × {t : ℝ // |t| < r}) ≃ₜ
      {x : E // x ∈ S ∧ |f x| < r} := by
  have hrR : r < R := by linarith
  have hforward (x : {x : E // x ∈ S ∧ f x = 0}) (t : {t : ℝ // |t| < r}) :
      f (φ.toFun (x.1,t.1)) = t.1 := by
    have he := φ.translate_level_on hf hS hC hR x.2.1 (t := t.1)
    simpa only [x.2.2, abs_zero, zero_add] using
      he (by rw [x.2.2, abs_zero, zero_add]; exact t.2.trans hrR)
  have hbackward (y : {x : E // x ∈ S ∧ |f x| < r}) :
      f (φ.toFun (y.1,-f y.1)) = 0 := by
    have he := φ.translate_level_on hf hS hC hR y.2.1 (t := -f y.1)
      (by rw [abs_neg]; linarith [y.2.2])
    simpa only [add_neg_cancel] using he
  let a : ({x : E // x ∈ S ∧ f x = 0} × {t : ℝ // |t| < r}) →
      {x : E // x ∈ S ∧ |f x| < r} := fun p =>
    ⟨φ.toFun (p.1.1,p.2.1), hS p.1.1 p.1.2.1 p.2.1,
      by rw [hforward]; exact p.2.2⟩
  let b : {x : E // x ∈ S ∧ |f x| < r} →
      ({x : E // x ∈ S ∧ f x = 0} × {t : ℝ // |t| < r}) := fun y =>
    (⟨φ.toFun (y.1,-f y.1), hS y.1 y.2.1 _, hbackward y⟩,
     ⟨f y.1,y.2.2⟩)
  refine ⟨⟨a,b,?_,?_⟩,?_,?_⟩
  · intro p
    apply Prod.ext
    · apply Subtype.ext
      change φ.toFun (φ.toFun (p.1.1,p.2.1),-f (φ.toFun (p.1.1,p.2.1))) = p.1.1
      rw [hforward, φ.add hK, add_neg_cancel, φ.initial]
    · apply Subtype.ext
      exact hforward p.1 p.2
  · intro y
    apply Subtype.ext
    change φ.toFun (φ.toFun (y.1,-f y.1),f y.1) = y.1
    rw [φ.add hK, neg_add_cancel, φ.initial]
  · apply Continuous.subtype_mk
    exact φ.continuous_toFun.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  · apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact φ.continuous_toFun.comp
        (continuous_subtype_val.prodMk (hf.continuous.comp continuous_subtype_val).neg)
    · apply Continuous.subtype_mk
      exact hf.continuous.comp continuous_subtype_val

lemma observable_monotone {f : E → ℝ} (hf : Differentiable ℝ f)
    {S : Set E} (hS : ∀ x ∈ S, ∀ t, φ.toFun (x,t) ∈ S)
    (hF : ∀ x ∈ S, 0 ≤ fderiv ℝ f x (F x)) {x : E} (hx : x ∈ S) :
    Monotone (fun t => f (φ.toFun (x,t))) := by
  have hd (t : ℝ) := (hf (φ.toFun (x,t))).hasFDerivAt.comp_hasDerivAt t
    (φ.derivative x t)
  apply monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt)
  intro t
  rw [(hd t).deriv]
  exact hF _ (hS x hx t)

def negativeHomotopyEquiv {f : E → ℝ} (hf : Differentiable ℝ f)
    {S : Set E} (hS : ∀ x ∈ S, ∀ t, φ.toFun (x,t) ∈ S)
    (hF : ∀ x ∈ S, fderiv ℝ f x (F x) ∈ Icc (0:ℝ) 1)
    {R δ : ℝ} (hδ : 0 < δ) (hδR : δ < R)
    (hR : ∀ x ∈ S, |f x| < R → fderiv ℝ f x (F x) = 1) :
    ContinuousMap.HomotopyEquiv {x : E // x ∈ S ∧ f x ≤ 0}
      {x : E // x ∈ S ∧ f x < 0} := by
  have hC (x : E) (hx : x ∈ S) : ‖fderiv ℝ f x (F x)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hF x hx).1]
    exact (hF x hx).2
  have hnoninc (x : E) (hx : x ∈ S) {t : ℝ} (ht : t ≤ 0) :
      f (φ.toFun (x,t)) ≤ f x := by
    simpa only [φ.initial] using φ.observable_monotone hf hS (fun x hx => (hF x hx).1) hx ht
  have hpush (x : E) (hx : x ∈ S) (hfx : f x ≤ 0) : f (φ.toFun (x,-δ)) < 0 := by
    rcases lt_or_eq_of_le hfx with hneg | heq
    · exact (hnoninc x hx (neg_nonpos.mpr hδ.le)).trans_lt hneg
    · have he := φ.translate_level_on hf hS hC hR hx (t := -δ) (by
        rw [heq,abs_zero,zero_add,abs_neg,abs_of_pos hδ]; exact hδR)
      rw [he,heq,zero_add]
      exact neg_neg_of_pos hδ
  let a : C({x : E // x ∈ S ∧ f x ≤ 0},{x : E // x ∈ S ∧ f x < 0}) :=
    ⟨fun x => ⟨φ.toFun (x.1,-δ),hS _ x.2.1 _,hpush _ x.2.1 x.2.2⟩,
      (φ.continuous_toFun.comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _⟩
  let b : C({x : E // x ∈ S ∧ f x < 0},{x : E // x ∈ S ∧ f x ≤ 0}) :=
    ⟨fun x => ⟨x.1,x.2.1,x.2.2.le⟩, continuous_subtype_val.subtype_mk _⟩
  have htime (t : unitInterval) : -(1-(t:ℝ))*δ ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr t.2.2)) hδ.le
  refine { toFun := a, invFun := b, left_inv := ⟨?_⟩, right_inv := ⟨?_⟩ }
  · refine { toFun := fun tx => ⟨φ.toFun (tx.2.1,-(1-(tx.1:ℝ))*δ),
               hS _ tx.2.2.1 _, (hnoninc _ tx.2.2.1 (htime tx.1)).trans tx.2.2.2⟩
             continuous_toFun := ?_
             map_zero_left := ?_
             map_one_left := ?_ }
    · apply Continuous.subtype_mk
      exact φ.continuous_toFun.comp ((continuous_subtype_val.comp continuous_snd).prodMk
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).neg.mul continuous_const))
    · intro x; apply Subtype.ext; simp [a,b]
    · intro x; apply Subtype.ext; simp [φ.initial]
  · refine { toFun := fun tx => ⟨φ.toFun (tx.2.1,-(1-(tx.1:ℝ))*δ),
               hS _ tx.2.2.1 _, (hnoninc _ tx.2.2.1 (htime tx.1)).trans_lt tx.2.2.2⟩
             continuous_toFun := ?_
             map_zero_left := ?_
             map_one_left := ?_ }
    · apply Continuous.subtype_mk
      exact φ.continuous_toFun.comp ((continuous_subtype_val.comp continuous_snd).prodMk
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).neg.mul continuous_const))
    · intro x; apply Subtype.ext; simp [a,b]
    · intro x; apply Subtype.ext; simp [φ.initial]

end NearbyLagrangian.ODE.CompleteFlow

namespace NearbyLagrangian.Tubes.RegularHomogeneous
open Set Filter Metric
open scoped Topology InnerProductSpace ContDiff NNReal
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Nontrivial W]

theorem exists_sphere_level_collar (f : RegularHomogeneous W) (hf : f.SmoothOffZero) :
    ∃ r > 0, Nonempty
      (({w : W // ‖w‖ = 1 ∧ f w = 0} × {t : ℝ // |t| < r}) ≃ₜ
        {w : W // ‖w‖ = 1 ∧ |f w| < r}) := by
  obtain ⟨R,hR,F,hFs,hFc,hFt,hFb,hFr⟩ := f.exists_compact_tangent_field hf
  obtain ⟨L,K,hL,hK⟩ := ODE.compact_field_bounds hFc (hFs.of_le (by simp))
  obtain ⟨φ⟩ := ODE.exists_completeFlow F hL hK
  have hS (x : W) (hx : x ∈ {w : W | ‖w‖ = 1}) (t : ℝ) :
      φ.toFun (x,t) ∈ {w : W | ‖w‖ = 1} := by
    change ‖φ.toFun (x,t)‖ = 1
    rw [φ.norm_eq hFt, hx]
  have hC (x : W) (hx : x ∈ {w : W | ‖w‖ = 1}) :
      ‖fderiv ℝ f x (F x)‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hFb x hx).1]
    exact (hFb x hx).2
  refine ⟨R/3,by positivity,⟨?_⟩⟩
  exact φ.levelCollarOn hK f.differentiable hS hC (by positivity)
    (by linarith) hFr

theorem exists_negative_open_equiv (f : RegularHomogeneous W) (hf : f.SmoothOffZero) :
    Nonempty (ContinuousMap.HomotopyEquiv
      {w : W // ‖w‖ = 1 ∧ f w ≤ 0} {w : W // ‖w‖ = 1 ∧ f w < 0}) := by
  obtain ⟨R,hR,F,hFs,hFc,hFt,hFb,hFr⟩ := f.exists_compact_tangent_field hf
  obtain ⟨φ⟩ := ODE.exists_completeFlow_of_compact hFc (hFs.of_le (by simp))
  have hS (x : W) (hx : x ∈ {w : W | ‖w‖ = 1}) (t : ℝ) :
      φ.toFun (x,t) ∈ {w : W | ‖w‖ = 1} := by
    change ‖φ.toFun (x,t)‖ = 1
    rw [φ.norm_eq hFt, hx]
  exact ⟨φ.negativeHomotopyEquiv f.differentiable hS hFb
    (δ := R/2) (by positivity) (by linarith) hFr⟩

end NearbyLagrangian.Tubes.RegularHomogeneous

end

end OAI
