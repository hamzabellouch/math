import Mathlib
import OAI.Geometry.NearbyLagrangian.SphereFields
import OAI.Geometry.NearbyLagrangian.ParameterFlows

namespace OAI

/-! Smooth tangent-band flows and equivalence of close negative families. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes.RegularHomogeneous
open Set Filter Metric
open scoped Topology InnerProductSpace ContDiff
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

def bandBump (c : ℝ) (hc : 0 < c) : ContDiffBump (0:ℝ) :=
  ⟨c/16,c/8,by positivity,by linarith⟩

def radialShellOuter : ContDiffBump (0:W) := ⟨2,3,by norm_num,by norm_num⟩
def radialShellInner : ContDiffBump (0:W) := ⟨1/4,1/2,by norm_num,by norm_num⟩
def radialShell (w : W) : ℝ := (radialShellOuter (W:=W)) w * (1-(radialShellInner (W:=W)) w)

omit [CompleteSpace W] in
lemma radialShell_sphere {w : W} (hw : ‖w‖ = 1) : radialShell w = 1 := by
  have ho : (radialShellOuter (W:=W)) w = 1 := (radialShellOuter (W:=W)).one_of_mem_closedBall (by
    simpa only [mem_closedBall,dist_zero_right,hw,radialShellOuter] using
      (show (1:ℝ) ≤ 2 by norm_num))
  have hi : (radialShellInner (W:=W)) w = 0 := (radialShellInner (W:=W)).zero_of_le_dist (by
    simpa only [dist_zero_right,hw,radialShellInner] using (show (1:ℝ)/2 ≤ 1 by norm_num))
  simp only [radialShell,ho,hi,sub_zero,mul_one]

def tangentBandField (g : RegularHomogeneous W) (c : ℝ) (hc : 0 < c) (w : W) : W :=
  (radialShell w * bandBump c hc (g w)) • g.tangentGradient w

lemma tangentBandField_radial (g : RegularHomogeneous W) {c : ℝ} (hc : 0 < c) (w : W) :
    ⟪w,g.tangentBandField c hc w⟫_ℝ = 0 := by
  simp only [tangentBandField,real_inner_smul_right,g.inner_tangentGradient,mul_zero]

lemma tangentBandField_zero (g : RegularHomogeneous W) {c : ℝ} (hc : 0 < c)
    {w : W} (hw : 3 ≤ ‖w‖) : g.tangentBandField c hc w = 0 := by
  have ho : (radialShellOuter (W:=W)) w = 0 := (radialShellOuter (W:=W)).zero_of_le_dist (by
    simpa only [dist_zero_right,radialShellOuter] using hw)
  simp only [tangentBandField,radialShell,ho,zero_mul,zero_smul]

lemma tangentGradient_lower {g : RegularHomogeneous W} {c : ℝ} (hc : 0 < c)
    {w : W} (hw : ‖w‖ = 1) (hg : c ≤ ‖gradient g w‖) (hb : |g w| ≤ c/8) :
    c^2/2 ≤ ‖g.tangentGradient w‖^2 ∧ c/2 ≤ ‖g.tangentGradient w‖ := by
  have hq : ‖g.tangentGradient w‖^2 = ‖gradient g w‖^2 - 4*(g w)^2 := by
    rw [← g.tangentGradient_on_sphere hw,g.fderiv_tangentGradient,hw,one_pow,one_mul]
  have hb' : (g w)^2 ≤ (c/8)^2 := by
    nlinarith [sq_abs (g w),abs_nonneg (g w)]
  have hlow : c^2/2 ≤ ‖g.tangentGradient w‖^2 := by
    nlinarith [sq_nonneg (‖gradient g w‖-c)]
  refine ⟨hlow,?_⟩
  nlinarith [norm_nonneg (g.tangentGradient w)]

lemma tangentBandField_transverse {f g : RegularHomogeneous W} {c ε : ℝ}
    (hc : 0 < c) (hεc : ε ≤ c/32) {w : W} (hw : ‖w‖ = 1)
    (hg : c ≤ ‖gradient g w‖) (hval : |f w-g w| ≤ ε)
    (hder : ‖fderiv ℝ f w - fderiv ℝ g w‖ ≤ ε) :
    0 ≤ fderiv ℝ f w (g.tangentBandField c hc w) ∧
      (|f w| ≤ ε → c^2/4 ≤ fderiv ℝ f w (g.tangentBandField c hc w)) := by
  have he : fderiv ℝ f w (g.tangentBandField c hc w) =
      bandBump c hc (g w) * fderiv ℝ f w (g.tangentGradient w) := by
    simp only [tangentBandField,radialShell_sphere hw,one_mul,map_smul,smul_eq_mul]
  have hpert : |fderiv ℝ f w (g.tangentGradient w)-‖g.tangentGradient w‖^2| ≤
      ε*‖g.tangentGradient w‖ := by
    rw [← g.tangentGradient_on_sphere hw]
    have h := (fderiv ℝ f w - fderiv ℝ g w).le_opNorm (g.tangentGradient w)
    exact h.trans (mul_le_mul_of_nonneg_right hder (norm_nonneg _))
  have hband (hb : |g w| ≤ c/8) :
      c^2/4 ≤ fderiv ℝ f w (g.tangentGradient w) := by
    obtain ⟨hT,hT'⟩ := tangentGradient_lower hc hw hg hb
    have hp := (abs_le.mp hpert).1
    have hE : ε*‖g.tangentGradient w‖ ≤ ‖g.tangentGradient w‖^2/2 := by
      nlinarith [mul_nonneg (norm_nonneg (g.tangentGradient w)) (show
        0 ≤ ‖g.tangentGradient w‖/2-ε by linarith)]
    linarith
  rw [he]
  constructor
  · by_cases hz : bandBump c hc (g w) = 0
    · simp only [hz,zero_mul,le_refl]
    · have hb : |g w| ≤ c/8 := by
        by_contra h
        apply hz
        apply (bandBump c hc).zero_of_le_dist
        simpa only [dist_zero_right,Real.norm_eq_abs,bandBump] using (not_le.mp h).le
      exact mul_nonneg (bandBump c hc).nonneg ((div_nonneg (sq_nonneg c) (by norm_num : (0:ℝ) ≤ 4)).trans (hband hb))
  · intro hfw
    have hb : |g w| ≤ c/16 := by
      have hv := abs_le.mp hval
      have hf := abs_le.mp hfw
      apply abs_le.mpr
      constructor <;> linarith
    have hχ : bandBump c hc (g w) = 1 := (bandBump c hc).one_of_mem_closedBall (by
      simpa only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,bandBump] using hb)
    rw [hχ,one_mul]
    exact hband (hb.trans (by linarith))

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes.RegularHomogeneous
open Set Filter Metric
open scoped Topology InnerProductSpace ContDiff Manifold
variable {E W B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [TopologicalSpace B] [ChartedSpace E B] [IsManifold 𝓘(ℝ,E) ∞ B]

lemma contMDiff_tangentBandField {g : B → RegularHomogeneous W}
    (hg : SmoothFamily (E:=E) g) {c : ℝ} (hc : 0 < c) :
    ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,W)) 𝓘(ℝ,W) ∞
      (fun p : B × W => (g p.1).tangentBandField c hc p.2) := by
  intro p
  by_cases hp : p.2 = 0
  · apply (contMDiffAt_const (c := (0:W))).congr_of_eventuallyEq
    have hn : ∀ᶠ y : B × W in 𝓝 p, ‖y.2‖ < 1/4 :=
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const).mem_nhds (by
        change ‖p.2‖ < (1:ℝ)/4
        rw [hp,norm_zero]
        norm_num)
    filter_upwards [hn] with y hy
    have hi : (radialShellInner (W:=W)) y.2 = 1 :=
      (radialShellInner (W:=W)).one_of_mem_closedBall (by
        simpa only [mem_closedBall,dist_zero_right,radialShellInner] using hy.le)
    simp only [tangentBandField,radialShell,hi,sub_self,mul_zero,zero_mul,zero_smul]
  · have hval := hg p hp
    have hgrad := contMDiffAt_family_gradient hval
    have hn : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,W)) 𝓘(ℝ,ℝ) ∞
        (fun y : B × W => ‖y.2‖^2) p :=
      (contDiff_norm_sq (𝕜:=ℝ)).contDiffAt.comp_contMDiffAt contMDiffAt_snd
    have hT : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,W)) 𝓘(ℝ,W) ∞
        (fun y : B × W => (g y.1).tangentGradient y.2) p :=
      (hn.smul hgrad).sub ((contMDiffAt_const.mul hval).smul contMDiffAt_snd)
    have hψ : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,W)) 𝓘(ℝ,ℝ) ∞
        (fun y : B × W => radialShell y.2) p :=
      ((radialShellOuter (W:=W)).contDiff.contDiffAt.comp_contMDiffAt contMDiffAt_snd).mul
        (contMDiffAt_const.sub ((radialShellInner (W:=W)).contDiff.contDiffAt.comp_contMDiffAt
          contMDiffAt_snd))
    exact (hψ.mul ((bandBump c hc).contDiff.contDiffAt.comp_contMDiffAt hval)).smul hT

omit [CompleteSpace W] in

lemma contMDiff_family_spatial_fderiv {F : B × W → W}
    (hF : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,W)) 𝓘(ℝ,W) ∞ F) :
    ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,W)) 𝓘(ℝ,W →L[ℝ] W) ∞
      (fun p : B × W => fderiv ℝ (fun w => F (p.1,w)) p.2) := by
  intro p
  let A : (B × W) → W → W := fun x w => F (x.1,w)
  have hA : ContMDiffAt ((𝓘(ℝ,E).prod 𝓘(ℝ,W)).prod 𝓘(ℝ,W)) 𝓘(ℝ,W) ∞
      (Function.uncurry A) (p,p.2) :=
    (hF p).comp (p,p.2) ((contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)
  have h := hA.mfderiv (m:=∞) A Prod.snd contMDiffAt_snd (by simp)
  erw [inTangentCoordinates_model_space] at h
  simpa only [A,mfderiv_eq_fderiv] using h

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.ODE
open Set Filter Metric
open scoped Topology NNReal ContDiff
variable {B E : Type*} [TopologicalSpace B] [CompactSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem param_compact_field_bounds {F : B × E → E} (hF : Continuous F)
    (hDiff : ∀ b, Differentiable ℝ (fun x => F (b,x)))
    (hD : Continuous (fun p : B × E => fderiv ℝ (fun x => F (p.1,x)) p.2))
    {R : ℝ} (hR : ∀ b x, R ≤ ‖x‖ → F (b,x) = 0) :
    ∃ L K : ℝ≥0, (∀ b x, ‖F (b,x)‖ ≤ L) ∧
      ∀ b, LipschitzWith K (fun x => F (b,x)) := by
  let S : Set (B × E) := univ ×ˢ closedBall (0:E) (max R 0+1)
  have hS : IsCompact S := isCompact_univ.prod (isCompact_closedBall _ _)
  obtain ⟨L,hL⟩ := hS.exists_bound_of_continuousOn hF.continuousOn
  obtain ⟨K,hK⟩ := hS.exists_bound_of_continuousOn hD.continuousOn
  let L' : ℝ≥0 := ⟨max L 0,le_max_right _ _⟩
  let K' : ℝ≥0 := ⟨max K 0,le_max_right _ _⟩
  have hout (b : B) (x : E) (hx : x ∉ closedBall (0:E) (max R 0+1)) :
      (fun y => F (b,y)) =ᶠ[𝓝 x] (fun _ => (0:E)) := by
    have hx' : R < ‖x‖ := by
      simp only [mem_closedBall,dist_zero_right,not_le] at hx
      linarith [le_max_left R 0]
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx'] with y hy
    exact hR b y hy.le
  refine ⟨L',K',?_,?_⟩
  · intro b x
    by_cases hx : x ∈ closedBall (0:E) (max R 0+1)
    · exact (hL (b,x) ⟨mem_univ _,hx⟩).trans (le_max_left L 0)
    · have he := (hout b x hx).eq_of_nhds
      rw [he,norm_zero]
      exact L'.coe_nonneg
  · intro b
    apply lipschitzWith_of_nnnorm_fderiv_le (hDiff b)
    intro x
    by_cases hx : x ∈ closedBall (0:E) (max R 0+1)
    · exact_mod_cast (hK (b,x) ⟨mem_univ _,hx⟩).trans (le_max_left K 0)
    · rw [(hasFDerivAt_const (0:E) x).congr_of_eventuallyEq (hout b x hx) |>.fderiv]
      simp

end NearbyLagrangian.ODE

namespace NearbyLagrangian.Tubes.RegularHomogeneous
open Set Filter Metric
open scoped Topology InnerProductSpace ContDiff NNReal Manifold
variable {E W B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [TopologicalSpace B] [CompactSpace B] [ChartedSpace E B] [IsManifold 𝓘(ℝ,E) ∞ B]

theorem close_negative_family_equiv {f g : B → RegularHomogeneous W}
    (hg : SmoothFamily (E:=E) g) {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε)
    (hεc : ε ≤ c/32) (hgrad : ∀ b w, ‖w‖ = 1 → c ≤ ‖gradient (g b) w‖)
    (hval : ∀ b w, ‖w‖ = 1 → |f b w-g b w| ≤ ε)
    (hder : ∀ b w, ‖w‖ = 1 → ‖fderiv ℝ (f b) w-fderiv ℝ (g b) w‖ ≤ ε) :
    Nonempty (FiberwiseHomotopyEquiv
      (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => f p.1 p.2))
      (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => g p.1 p.2))) := by
  let F : B × W → W := fun p => (g p.1).tangentBandField c hc p.2
  have hF : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,W)) 𝓘(ℝ,W) ∞ F :=
    contMDiff_tangentBandField hg hc
  have hFs (b : B) : Differentiable ℝ (fun w => F (b,w)) := by
    have h := hF.comp ((contMDiff_const (c:=b)).prodMk (contMDiff_id (I:=𝓘(ℝ,W))))
    exact (contMDiff_iff_contDiff.mp h).differentiable (by simp)
  have hD : Continuous (fun p : B × W => fderiv ℝ (fun w => F (p.1,w)) p.2) :=
    (contMDiff_family_spatial_fderiv hF).continuous
  obtain ⟨L,K,hL,hK⟩ := ODE.param_compact_field_bounds hF.continuous hFs hD
    (R:=3) (fun b w hw => (g b).tangentBandField_zero hc hw)
  obtain ⟨φ⟩ := ODE.exists_paramCompleteFlow F hF.continuous hL hK
  have hS (b : B) (w : W) (hw : w ∈ {w : W | ‖w‖ = 1}) (t : ℝ) :
      φ.toFun ((b,w),t) ∈ {w : W | ‖w‖ = 1} := by
    change ‖(φ.specialize b).toFun (w,t)‖ = 1
    rw [(φ.specialize b).norm_eq (fun w => (g b).tangentBandField_radial hc w),hw]
  have hfT (b : B) (w : W) (hw : ‖w‖ = 1) :
      0 ≤ fderiv ℝ (f b) w (F (b,w)) ∧
      (|f b w| ≤ ε → c^2/4 ≤ fderiv ℝ (f b) w (F (b,w))) :=
    tangentBandField_transverse hc hεc hw (hgrad b w hw) (hval b w hw) (hder b w hw)
  have hgT (b : B) (w : W) (hw : ‖w‖ = 1) :
      0 ≤ fderiv ℝ (g b) w (F (b,w)) ∧
      (|g b w| ≤ ε → c^2/4 ≤ fderiv ℝ (g b) w (F (b,w))) :=
    tangentBandField_transverse hc hεc hw (hgrad b w hw)
      (by simpa only [sub_self,abs_zero] using hε)
      (by simpa only [sub_self,norm_zero] using hε)
  have htime : 2*ε ≤ (c^2/4)*(8*ε/c^2) := by
    have he : (c^2/4)*(8*ε/c^2) = 2*ε := by
      field_simp [hc.ne']
      ring
    rw [he]
  exact ⟨pairedNegativeFlowEquiv φ hK hS (fun b => (f b).differentiable)
    (fun b => (g b).differentiable) (fun b w hw => (hfT b w hw).1)
    (fun b w hw => (hgT b w hw).1) hε (by positivity) htime
    (fun b w hw => (hfT b w hw).2) (fun b w hw => (hgT b w hw).2) hval⟩

end NearbyLagrangian.Tubes.RegularHomogeneous

end

end OAI
