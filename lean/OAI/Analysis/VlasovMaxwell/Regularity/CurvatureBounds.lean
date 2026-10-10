import Mathlib
import OAI.Analysis.VlasovMaxwell.LocalPDE.EquationsBefore
import OAI.Analysis.VlasovMaxwell.LocalPDE.PicardContraction

namespace OAI

noncomputable section

namespace RVM

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

def CurvatureBound {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (f : U → W) (C : ℝ) : Prop :=
  ∀ x h, ‖f (x+h)+f (x-h)-(2:ℝ) • f x‖≤C*‖h‖^2

lemma taylor_remainder_of_fderiv_lipschitz {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} (hf : Differentiable ℝ f) {H : ℝ} (hH : 0≤H)
    (hD : ∀ x y, ‖fderiv ℝ f y-fderiv ℝ f x‖≤H*‖y-x‖) (x y : U) :
    ‖f y-f x-fderiv ℝ f x (y-x)‖≤H*‖y-x‖^2 := by
  have h := (convex_closedBall x ‖y-x‖).norm_image_sub_le_of_norm_fderiv_le'
    (f:=f) (φ:=fderiv ℝ f x) (C:=H*‖y-x‖) (fun z _ => hf z)
    (fun z hz => (hD x z).trans (mul_le_mul_of_nonneg_left
      (by simpa only [mem_closedBall,dist_eq_norm] using hz) hH))
    (show x∈closedBall x ‖y-x‖ by simp)
    (show y∈closedBall x ‖y-x‖ by simp only [mem_closedBall,dist_eq_norm,le_refl])
  exact h.trans_eq (by ring)

lemma curvature_of_fderiv_lipschitz {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} (hf : Differentiable ℝ f) {H : ℝ} (hH : 0≤H)
    (hD : ∀ x y, ‖fderiv ℝ f y-fderiv ℝ f x‖≤H*‖y-x‖) : CurvatureBound f (2*H) := by
  intro x v
  have hp := taylor_remainder_of_fderiv_lipschitz hf hH hD x (x+v)
  have hm := taylor_remainder_of_fderiv_lipschitz hf hH hD x (x-v)
  simp only [add_sub_cancel_left,sub_sub_cancel_left,norm_neg,map_neg] at hp hm
  have he : f (x+v)+f (x-v)-(2:ℝ) • f x =
      (f (x+v)-f x-fderiv ℝ f x v)+(f (x-v)-f x+fderiv ℝ f x v) := by module
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add hp (by simpa only [sub_neg_eq_add] using hm))).trans_eq (by ring)

lemma smooth_compact_curvature {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → W}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ H : ℝ, 0≤H ∧ CurvatureBound f H := by
  obtain ⟨H,hH,hD⟩ := smooth_compact_lipschitz
    (hf.fderiv_right (by decide)) (hc.fderiv ℝ)
  exact ⟨2*H,by positivity,curvature_of_fderiv_lipschitz (hf.differentiable (by simp)) hH hD⟩

lemma CurvatureBound.triple {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H L : ℝ} (hc : CurvatureBound f H) (hH : 0≤H) (_hL : 0≤L)
    (hl : ∀ x y, ‖f y-f x‖≤L*‖y-x‖) (a b c : U) :
    ‖f a+f b-(2:ℝ) • f c‖≤H*‖a-b‖^2+L*‖a+b-(2:ℝ) • c‖ := by
  let m := (1/2:ℝ) • (a+b)
  let v := (1/2:ℝ) • (a-b)
  have hp : m+v=a := by dsimp [m,v]; module
  have hm : m-v=b := by dsimp [m,v]; module
  have hb := hc m v
  rw [hp,hm] at hb
  have hv : ‖v‖≤‖a-b‖ := by dsimp [v]; rw [norm_smul,Real.norm_eq_abs]; norm_num; nlinarith [norm_nonneg (a-b)]
  have hmd : (2:ℝ) • (m-c)=a+b-(2:ℝ) • c := by dsimp [m]; module
  have hde : f a+f b-(2:ℝ) • f c =
      (f a+f b-(2:ℝ) • f m)+(2:ℝ) • (f m-f c) := by module
  rw [hde]
  have hh := hl c m
  have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤2)
  have hscale : 2*‖m-c‖=‖a+b-(2:ℝ) • c‖ := by rw [← hmd,norm_smul,Real.norm_eq_abs]; norm_num
  have hscale' := congrArg (fun r : ℝ => L*r) hscale
  have hnorm : ‖(2:ℝ) • (f m-f c)‖≤L*‖a+b-(2:ℝ) • c‖ := by
    rw [norm_smul,Real.norm_eq_abs]; norm_num
    nlinarith [hh',hscale']
  exact (norm_add_le _ _).trans (add_le_add (hb.trans
    (mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hv) hH)) hnorm)

lemma CurvatureBound.comp {U V W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : V → W} {g : U → V}
    {H L M K : ℝ} (hf : CurvatureBound f H) (hg : CurvatureBound g K)
    (hH : 0≤H) (hL : 0≤L) (hM : 0≤M)
    (hfl : ∀ x y, ‖f y-f x‖≤L*‖y-x‖)
    (hgl : ∀ x y, ‖g y-g x‖≤M*‖y-x‖) :
    CurvatureBound (f ∘ g) (4*H*M^2+L*K) := by
  intro x v
  have ht := hf.triple hH hL hfl (g (x+v)) (g (x-v)) (g x)
  have hdist : ‖g (x+v)-g (x-v)‖≤2*M*‖v‖ := by
    have hh := hgl (x-v) (x+v)
    rw [show x+v-(x-v)=(2:ℝ) • v by module,norm_smul,Real.norm_eq_abs] at hh
    norm_num at hh
    nlinarith [hh]
  apply ht.trans
  have hd := mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*M*‖v‖)).mpr hdist) hH
  have hh := mul_le_mul_of_nonneg_left (hg x v) hL
  nlinarith [hd,hh]

lemma inverse_q_lipschitz (v w : Vec) : |(q w)⁻¹-(q v)⁻¹|≤‖w-v‖ := by
  have hv : 1≤q v := by nlinarith [q_sq v,q_pos v,sq_nonneg ‖v‖]
  have hw : 1≤q w := by nlinarith [q_sq w,q_pos w,sq_nonneg ‖w‖]
  have he : (q w)⁻¹-(q v)⁻¹=(q v-q w)/(q w*q v) := by field_simp
  rw [he,abs_div,abs_of_pos (mul_pos (q_pos w) (q_pos v)),abs_sub_comm]
  exact (div_le_self (abs_nonneg _) (by nlinarith : 1≤q w*q v)).trans (q_lipschitz v w)

lemma velocityProjection_parameter_lipschitz {u v : Vec} (hu : ‖u‖≤1) (hv : ‖v‖≤1) (h : Vec) :
    ‖velocityProjection u h-velocityProjection v h‖≤2*‖u-v‖*‖h‖ := by
  have he : velocityProjection u h-velocityProjection v h=
      -(dot (u-v) h • u+dot v h • (u-v)) := by
    simp only [velocityProjection,dot_sub_left,sub_smul,smul_sub]
    module
  rw [he,norm_neg]
  have h₁ : ‖dot (u-v) h • u‖≤‖u-v‖*‖h‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul (abs_dot_le _ _) hu (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have h₂ : ‖dot v h • (u-v)‖≤‖u-v‖*‖h‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    have hh := mul_le_mul_of_nonneg_right ((abs_dot_le v h).trans
      (mul_le_mul_of_nonneg_right hv (norm_nonneg h))) (norm_nonneg (u-v))
    exact hh.trans_eq (by ring)
  exact ((norm_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by ring)

lemma fderiv_velocity_lipschitz (v w : Vec) :
    ‖fderiv ℝ velocity w-fderiv ℝ velocity v‖≤3*‖w-v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  have hu := (norm_velocity_lt_one w).le
  have hv := (norm_velocity_lt_one v).le
  have hh : (1:ℝ)≤q v := by nlinarith [q_sq v,q_pos v,sq_nonneg ‖v‖]
  have hq : 0≤(q v)⁻¹ := inv_nonneg.mpr (q_pos v).le
  have hq1 : (q v)⁻¹≤1 := (inv_le_one₀ (q_pos v)).mpr hh
  have he : (fderiv ℝ velocity w-fderiv ℝ velocity v) h =
      ((q w)⁻¹-(q v)⁻¹) • velocityProjection (velocity w) h+
      (q v)⁻¹ • (velocityProjection (velocity w) h-velocityProjection (velocity v) h) := by
    simp only [sub_apply,fderiv_velocity_apply,velocityProjection,sub_smul,smul_sub]
    module
  rw [he]
  have h₁ : ‖((q w)⁻¹-(q v)⁻¹) • velocityProjection (velocity w) h‖≤‖w-v‖*‖h‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (inverse_q_lipschitz v w) (velocityProjection_norm _ _ hu)
      (norm_nonneg _) (norm_nonneg _)
  have h₂ : ‖(q v)⁻¹ • (velocityProjection (velocity w) h-velocityProjection (velocity v) h)‖≤
      2*‖w-v‖*‖h‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hq]
    have hp := (velocityProjection_parameter_lipschitz hu hv h).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (velocity_global_lipschitz v w)
        (by norm_num)) (norm_nonneg h))
    exact (mul_le_mul hq1 hp (norm_nonneg _) zero_le_one).trans_eq (by ring)
  exact ((norm_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by ring)

lemma velocity_curvature : CurvatureBound velocity 6 := by
  convert curvature_of_fderiv_lipschitz
    (contDiff_velocity.differentiable (by simp : (∞:ℕ∞ω)≠0)) (by norm_num : (0:ℝ)≤3)
    fderiv_velocity_lipschitz using 1
  norm_num

lemma CurvatureBound.precomp_linear {U V W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : V → W} {H : ℝ}
    (hf : CurvatureBound f H) (hH : 0≤H) (A : U →L[ℝ] V) (hA : ∀ v, ‖A v‖≤‖v‖) :
    CurvatureBound (f ∘ A) H := by
  intro x v
  simp only [Function.comp_def,map_add,map_sub]
  exact (hf (A x) (A v)).trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hA v)) hH)

lemma CurvatureBound.add {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f g : U → W} {H K : ℝ} (hf : CurvatureBound f H) (hg : CurvatureBound g K) :
    CurvatureBound (fun x => f x+g x) (H+K) := by
  intro x v
  have he : f (x+v)+g (x+v)+(f (x-v)+g (x-v))-(2:ℝ) • (f x+g x)=
      (f (x+v)+f (x-v)-(2:ℝ) • f x)+(g (x+v)+g (x-v)-(2:ℝ) • g x) := by module
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add (hf x v) (hg x v))).trans_eq (by ring)

lemma CurvatureBound.cross_product {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {f g : U → Vec} {A B L N H K : ℝ} (hf : CurvatureBound f H) (hg : CurvatureBound g K)
    (hA : 0≤A) (_hB : 0≤B) (hL : 0≤L) (_hN : 0≤N) (hH : 0≤H) (_hK : 0≤K)
    (hfb : ∀ x, ‖f x‖≤A) (hgb : ∀ x, ‖g x‖≤B)
    (hfl : ∀ x y, ‖f y-f x‖≤L*‖y-x‖) (hgl : ∀ x y, ‖g y-g x‖≤N*‖y-x‖) :
    CurvatureBound (fun x => cross (f x) (g x)) (H*B+A*K+2*L*N) := by
  intro x v
  have he : cross (f (x+v)) (g (x+v))+cross (f (x-v)) (g (x-v))-
      (2:ℝ) • cross (f x) (g x)=
      cross (f (x+v)+f (x-v)-(2:ℝ) • f x) (g x)+
      cross (f x) (g (x+v)+g (x-v)-(2:ℝ) • g x)+
      cross (f (x+v)-f x) (g (x+v)-g x)+cross (f (x-v)-f x) (g (x-v)-g x) := by
    ext i
    fin_cases i <;> simp [cross] <;> ring
  have h₁ := (norm_cross_le _ _).trans (mul_le_mul (hf x v) (hgb x) (norm_nonneg _) (by positivity))
  have h₂ := (norm_cross_le _ _).trans (mul_le_mul (hfb x) (hg x v) (norm_nonneg _) hA)
  have h₃ : ‖cross (f (x+v)-f x) (g (x+v)-g x)‖≤(L*‖v‖)*(N*‖v‖) := by
    have hp := hfl x (x+v)
    have hq := hgl x (x+v)
    simp only [add_sub_cancel_left] at hp hq
    exact (norm_cross_le _ _).trans (mul_le_mul hp hq (norm_nonneg _) (by positivity))
  have h₄ : ‖cross (f (x-v)-f x) (g (x-v)-g x)‖≤(L*‖v‖)*(N*‖v‖) := by
    have hp := hfl x (x-v)
    have hq := hgl x (x-v)
    simp only [sub_sub_cancel_left,norm_neg] at hp hq
    exact (norm_cross_le _ _).trans (mul_le_mul hp hq (norm_nonneg _) (by positivity))
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add h₁ h₂)) h₃)) h₄)).trans_eq (by ring)

lemma lorentzField_curvature {E B : Field} {t L N H : ℝ}
    (hL : 0≤L) (hN : 0≤N) (hH : 0≤H)
    (hBb : ∀ x, ‖B (t,x)‖≤L)
    (hBx : ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    (hEc : CurvatureBound (fun x => E (t,x)) H)
    (hBc : CurvatureBound (fun x => B (t,x)) H) :
    CurvatureBound (fun z => lorentzField E B (t,z)) (6+6*L+2*H+2*N) := by
  let u : Phase → Vec := fun z => velocity z.2
  let g : Phase → Vec := fun z => B (t,z.1)
  have hu : CurvatureBound u 6 := velocity_curvature.precomp_linear (by norm_num)
    (ContinuousLinearMap.snd ℝ Vec Vec) (fun z => norm_snd_le z)
  have hg : CurvatureBound g H := hBc.precomp_linear hH
    (ContinuousLinearMap.fst ℝ Vec Vec) (fun z => norm_fst_le z)
  have he : CurvatureBound (fun z : Phase => E (t,z.1)) H := hEc.precomp_linear hH
    (ContinuousLinearMap.fst ℝ Vec Vec) (fun z => norm_fst_le z)
  have hul (z w : Phase) : ‖u w-u z‖≤1*‖w-z‖ := by
    change ‖velocity w.2-velocity z.2‖≤1*‖w-z‖
    rw [one_mul]
    exact (velocity_global_lipschitz z.2 w.2).trans (norm_snd_le (w-z))
  have hgl (z w : Phase) : ‖g w-g z‖≤N*‖w-z‖ :=
    (hBx z.1 w.1).trans (mul_le_mul_of_nonneg_left (norm_fst_le (w-z)) hN)
  have hc := hu.cross_product hg (by norm_num) hL (by norm_num) hN (by norm_num) hH
    (fun z => (norm_velocity_lt_one z.2).le) (fun z => hBb z.1) hul hgl
  have hforce := he.add hc
  intro z v
  change ‖(u (z+v),E (t,(z+v).1)+cross (u (z+v)) (g (z+v)))+
    (u (z-v),E (t,(z-v).1)+cross (u (z-v)) (g (z-v)))-
    (2:ℝ) • (u z,E (t,z.1)+cross (u z) (g z))‖≤_
  rw [Prod.norm_def,max_le_iff]
  constructor
  · have hh := hu z v
    simp only [Prod.fst_sub,Prod.fst_add,Prod.smul_fst]
    nlinarith [hh,sq_nonneg ‖v‖,mul_nonneg hL (sq_nonneg ‖v‖),
      mul_nonneg hH (sq_nonneg ‖v‖),mul_nonneg hN (sq_nonneg ‖v‖)]
  · have hh := hforce z v
    simp only [Prod.snd_sub,Prod.snd_add,Prod.smul_snd]
    nlinarith [hh,sq_nonneg ‖v‖]

def SmoothLorentzFlow.reversePath {E B : Field} (F : SmoothLorentzFlow E B)
    (t : ℝ) (z : Phase) (u : ℝ) : Phase := F.forward (F.backward (t,z)) (t-u)

lemma SmoothLorentzFlow.reversePath_deriv {E B : Field} (F : SmoothLorentzFlow E B)
    (t u : ℝ) (z : Phase) :
    HasDerivAt (F.reversePath t z) (-lorentzField E B (t-u,F.reversePath t z u)) u := by
  change HasDerivAt (fun r => F.forward (F.backward (t,z)) (t-r))
    (-lorentzField E B (t-u,F.forward (F.backward (t,z)) (t-u))) u
  have hh := (F.ode (F.backward (t,z)) (t-u)).scomp u ((hasDerivAt_id u).const_sub t)
  simpa only [Function.comp_def,one_smul,neg_smul] using hh

@[simp] lemma SmoothLorentzFlow.reversePath_zero {E B : Field} (F : SmoothLorentzFlow E B)
    (t : ℝ) (z : Phase) : F.reversePath t z 0=z := by
  simp [SmoothLorentzFlow.reversePath,F.right_inverse]

@[simp] lemma SmoothLorentzFlow.reversePath_end {E B : Field} (F : SmoothLorentzFlow E B)
    (t : ℝ) (z : Phase) : F.reversePath t z t=F.backward (t,z) := by
  simp [SmoothLorentzFlow.reversePath,F.initial]

lemma SmoothLorentzFlow.reversePath_lipschitz {E B : Field} (F : SmoothLorentzFlow E B)
    {T L N : ℝ} (hL : 0≤L) (hN : 0≤N)
    (hB : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)‖≤L)
    (hEx : ∀ t∈Icc 0 T, ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
    (hBx : ∀ t∈Icc 0 T, ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    {t u : ℝ} (ht : t∈Icc 0 T) (hu : u∈Icc 0 t) (z z' : Phase) :
    ‖F.reversePath t z u-F.reversePath t z' u‖≤‖z-z'‖*Real.exp ((1+2*N+L)*u) := by
  let K := 1+2*N+L
  have hK : 0<K := by dsimp [K]; linarith
  have hfc : ContinuousOn (fun u => F.reversePath t z u-F.reversePath t z' u) (Icc 0 t) :=
    (continuous_iff_continuousAt.mpr fun u => (F.reversePath_deriv t u z).continuousAt).continuousOn.sub
      (continuous_iff_continuousAt.mpr fun u => (F.reversePath_deriv t u z').continuousAt).continuousOn
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hfc
    (fun u _ => ((F.reversePath_deriv t u z).sub (F.reversePath_deriv t u z')).hasDerivWithinAt)
    (K:=K) (ε:=0) (δ:=‖z-z'‖) (by simp)
    (fun v hv => by
      have htime : t-v∈Icc 0 T := ⟨by linarith [hv.2],by linarith [ht.2,hv.1]⟩
      have h := lorentzField_difference_bound (E':=E) (B':=B) hL hN (D:=0) le_rfl (hB _ htime) (hEx _ htime) (hBx _ htime)
        (by intros; simp) (by intros; simp) (F.reversePath t z v) (F.reversePath t z' v)
      simpa only [neg_sub_neg,norm_sub_rev,mul_zero,add_zero] using h) u hu
  exact hh.trans (by simpa only [zero_mul,add_zero,sub_zero] using
    gronwallBound_le_exp_linear hK (ε:=0) le_rfl hu.1 (δ:=‖z-z'‖))

lemma SmoothLorentzFlow.backward_curvature {E B : Field} (F : SmoothLorentzFlow E B)
    {T L N H : ℝ} (hL : 0≤L) (hN : 0≤N) (hH : 0≤H)
    (hB : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)‖≤L)
    (hEx : ∀ t∈Icc 0 T, ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
    (hBx : ∀ t∈Icc 0 T, ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    (hEc : ∀ t∈Icc 0 T, CurvatureBound (fun x => E (t,x)) H)
    (hBc : ∀ t∈Icc 0 T, CurvatureBound (fun x => B (t,x)) H)
    {t : ℝ} (ht : t∈Icc 0 T) :
    CurvatureBound (fun z => F.backward (t,z))
      (4*(6+6*L+2*H+2*N)*t*(Real.exp ((1+2*N+L)*T))^3) := by
  intro z v
  let K := 1+2*N+L
  let C := 6+6*L+2*H+2*N
  let Q := Real.exp (K*T)
  have hK : 0<K := by dsimp [K]; linarith
  have hC : 0≤C := by dsimp [C]; positivity
  have hQ : 0<Q := Real.exp_pos _
  let d : ℝ → Phase := fun u => F.reversePath t (z+v) u+F.reversePath t (z-v) u-
    (2:ℝ) • F.reversePath t z u
  let d' : ℝ → Phase := fun u => -lorentzField E B (t-u,F.reversePath t (z+v) u)-
    lorentzField E B (t-u,F.reversePath t (z-v) u)+(2:ℝ) • lorentzField E B (t-u,F.reversePath t z u)
  have hd (u : ℝ) : HasDerivAt d (d' u) u := by
    have hh := ((F.reversePath_deriv t u (z+v)).add (F.reversePath_deriv t u (z-v))).sub
      ((F.reversePath_deriv t u z).const_smul (2:ℝ))
    have he : d' u = -lorentzField E B (t-u,F.reversePath t (z+v) u)+
        -lorentzField E B (t-u,F.reversePath t (z-v) u)-
        (2:ℝ) • -lorentzField E B (t-u,F.reversePath t z u) := by dsimp [d']; module
    rw [he]
    exact hh
  have hdc : ContinuousOn d (Icc 0 t) :=
    (continuous_iff_continuousAt.mpr fun u => (hd u).continuousAt).continuousOn
  have hzero : ‖d 0‖≤0 := by
    have he : d 0=0 := by dsimp [d]; rw [F.reversePath_zero,F.reversePath_zero,F.reversePath_zero]; module
    rw [he,norm_zero]
  have hbound (u : ℝ) (hu : u∈Ico 0 t) : ‖d' u‖≤K*‖d u‖+4*C*Q^2*‖v‖^2 := by
    have htime : t-u∈Icc 0 T := ⟨by linarith [hu.2],by linarith [ht.2,hu.1]⟩
    have hforce := lorentzField_curvature hL hN hH (hB _ htime) (hBx _ htime) (hEc _ htime) (hBc _ htime)
    have hforceL (a b : Phase) : ‖lorentzField E B (t-u,b)-lorentzField E B (t-u,a)‖≤K*‖b-a‖ := by
      simpa only [mul_zero,add_zero] using lorentzField_difference_bound (E':=E) (B':=B) hL hN (D:=0) le_rfl
        (hB _ htime) (hEx _ htime) (hBx _ htime) (by intros; simp) (by intros; simp) b a
    have htr := hforce.triple hC hK.le hforceL
      (F.reversePath t (z+v) u) (F.reversePath t (z-v) u) (F.reversePath t z u)
    have hdist : ‖F.reversePath t (z+v) u-F.reversePath t (z-v) u‖≤2*‖v‖*Q := by
      have hh := F.reversePath_lipschitz hL hN hB hEx hBx ht (Ico_subset_Icc_self hu) (z+v) (z-v)
      rw [show z+v-(z-v)=(2:ℝ) • v by module,norm_smul,Real.norm_eq_abs] at hh
      norm_num at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (le_trans hu.2.le ht.2) hK.le)) (by positivity))
    have hdist2 := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*‖v‖*Q)).mpr hdist) hC
    have he : d' u=-(lorentzField E B (t-u,F.reversePath t (z+v) u)+
      lorentzField E B (t-u,F.reversePath t (z-v) u)-(2:ℝ) • lorentzField E B (t-u,F.reversePath t z u)) := by
      dsimp [d']; module
    rw [he,norm_neg]
    dsimp only [d]
    nlinarith [htr,hdist2]
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hdc
    (fun u _ => (hd u).hasDerivWithinAt) (K:=K) (ε:=4*C*Q^2*‖v‖^2) hzero hbound t ⟨ht.1,le_rfl⟩
  simp only [sub_zero] at hh
  have hε : 0≤4*C*Q^2*‖v‖^2 := by positivity
  have hfull := hh.trans (gronwallBound_le_exp_linear hK hε ht.1)
  simp only [d,F.reversePath_end,zero_add] at hfull
  have h_exp : Real.exp (K*t)≤Q := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK.le)
  have hfinal := hfull.trans (mul_le_mul_of_nonneg_left h_exp (mul_nonneg hε ht.1))
  exact hfinal.trans_eq (by dsimp [C,Q,K]; ring)

lemma CurvatureBound.mono {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H K : ℝ} (hf : CurvatureBound f H) (h : H≤K) : CurvatureBound f K :=
  fun x v => (hf x v).trans (mul_le_mul_of_nonneg_right h (sq_nonneg _))

lemma CurvatureBound.prodMk {U V W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → V} {g : U → W} {H : ℝ}
    (hf : CurvatureBound f H) (hg : CurvatureBound g H) :
    CurvatureBound (fun x => (f x,g x)) H := by
  intro x v
  exact max_le (hf x v) (hg x v)

lemma CurvatureBound.translate {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H : ℝ} (hf : CurvatureBound f H) (a : U) :
    CurvatureBound (fun x => f (x+a)) H := by
  intro x v
  convert hf (x+a) v using 1
  congr 2
  abel_nf

lemma transported_curvature {d : Datum} {s : Solution} {E B : Field}
    (hs : PicardRegular d s) (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hV : TransportFor s E B) {T A D L N H : ℝ}
    (hA : 0≤A) (hD : 0≤D) (hL : 0≤L) (hN : 0≤N) (hH : 0≤H)
    (ha : ∀ z w, ‖d.f₀ w-d.f₀ z‖≤A*‖w-z‖) (hdc : CurvatureBound d.f₀ D)
    (hBb : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)‖≤L)
    (hEx : ∀ t∈Icc 0 T, ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
    (hBx : ∀ t∈Icc 0 T, ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    (hEc : ∀ t∈Icc 0 T, CurvatureBound (fun x => E (t,x)) H)
    (hBc : ∀ t∈Icc 0 T, CurvatureBound (fun x => B (t,x)) H)
    {t : ℝ} (ht : t∈Icc 0 T) :
    CurvatureBound (fun z => s.f (t,z))
      (4*D*(Real.exp ((1+2*N+L)*T))^2+
        A*(4*(6+6*L+2*H+2*N)*t*(Real.exp ((1+2*N+L)*T))^3)) := by
  obtain ⟨F⟩ := exists_smoothLorentzFlow hE hB
  have hrep : (fun z => s.f (t,z))=d.f₀ ∘ (fun z => F.backward (t,z)) := by
    funext z
    rw [F.transport_for_inverse hs.smooth_f hV,hs.initial_f]
    rfl
  rw [hrep]
  apply hdc.comp (F.backward_curvature hL hN hH hBb hEx hBx hEc hBc ht) hD hA (Real.exp_pos _).le ha
  intro z w
  have hh := F.reversePath_lipschitz hL hN hBb hEx hBx ht (show t∈Icc 0 t from ⟨ht.1,le_rfl⟩) w z
  simp only [F.reversePath_end] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left ht.2 (by linarith : 0≤1+2*N+L))) (norm_nonneg _)).trans_eq (by ring))

lemma CurvatureBound.neg {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H : ℝ} (hf : CurvatureBound f H) : CurvatureBound (fun x => -f x) H := by
  intro x v
  simpa only [← neg_add,smul_neg,neg_sub_neg,norm_sub_rev] using hf x v

lemma CurvatureBound.sub {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f g : U → W} {H K : ℝ} (hf : CurvatureBound f H) (hg : CurvatureBound g K) :
    CurvatureBound (fun x => f x-g x) (H+K) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma CurvatureBound.const_smul {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H : ℝ} (hf : CurvatureBound f H) (a : ℝ) :
    CurvatureBound (fun x => a • f x) (|a| * H) := by
  intro x v
  rw [show a • f (x+v)+a • f (x-v)-(2:ℝ) • (a • f x)=
    a • (f (x+v)+f (x-v)-(2:ℝ) • f x) by module,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hf x v) (abs_nonneg a)).trans_eq (by ring)

lemma CurvatureBound.post_linear {U V W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → V} {H : ℝ}
    (hf : CurvatureBound f H) (A : V →L[ℝ] W) :
    CurvatureBound (fun x => A (f x)) (‖A‖*H) := by
  intro x v
  rw [← map_add,← map_smul,← map_sub]
  exact (A.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hf x v) (norm_nonneg _)).trans_eq (by ring))

lemma CurvatureBound.coordinate {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {f : U → Vec} {H : ℝ} (hf : CurvatureBound f H) (i : Fin 3) :
    CurvatureBound (fun x => f x i) H := by
  intro x v
  exact (norm_coordinate_le (f (x+v)+f (x-v)-(2:ℝ) • f x) i).trans (hf x v)

lemma CurvatureBound.spatial_slice {f : Phase → ℝ} {H : ℝ}
    (hf : CurvatureBound f H) (v : Vec) : CurvatureBound (fun x => f (x,v)) H := by
  intro x h
  simpa only [Prod.mk_add_mk,Prod.mk_sub_mk,add_zero,sub_zero,Prod.norm_mk,norm_zero,
    max_eq_left (norm_nonneg _)] using hf (x,v) (h,0)

lemma CurvatureBound.clm_apply_const {U V W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → (V →L[ℝ] W)} {H : ℝ}
    (hf : CurvatureBound f H) (a : V) :
    CurvatureBound (fun x => f x a) (H*‖a‖) := by
  intro x v
  have hh := (f (x+v)+f (x-v)-(2:ℝ) • f x).le_opNorm a
  exact hh.trans ((mul_le_mul_of_nonneg_right (hf x v) (norm_nonneg _)).trans_eq (by ring))

lemma CurvatureBound.integral {α U W : Type*} [MeasurableSpace α]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → U → W} {H : ℝ}
    (hint : ∀ x, Integrable (fun a => f a x) μ)
    (hf : ∀ᵐ a ∂μ, CurvatureBound (f a) H) :
    CurvatureBound (fun x => ∫ a, f a x ∂μ) (H*μ.real univ) := by
  intro x v
  have hadd : Integrable (fun a => f a (x+v)+f a (x-v)) μ := (hint (x+v)).add (hint (x-v))
  have hsmul : Integrable (fun a => (2:ℝ) • f a x) μ := (hint x).smul (2:ℝ)
  rw [← integral_add (hint (x+v)) (hint (x-v)),← integral_smul,← integral_sub hadd hsmul]
  exact (norm_integral_le_of_norm_le_const (hf.mono fun a ha => ha x v)).trans_eq (by ring)

lemma curvature_of_second_derivative_bound {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} (hf : ContDiff ℝ ∞ f) {H : ℝ} (hH : 0≤H)
    (hb : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖≤H) : CurvatureBound f (2*H) := by
  apply curvature_of_fderiv_lipschitz (hf.differentiable (by simp)) hH
  intro x y
  apply (convex_univ : Convex ℝ (univ : Set U)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hf.fderiv_right (by decide : (1:ℕ∞ω)+1≤∞)).differentiable (by norm_num) z) _ (mem_univ _) (mem_univ _)
  intro z _
  simpa only [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv] using hb z

lemma BoundedSmooth.spatial_curvature {F : Vec → Vec} (hF : BoundedSmooth F) :
    ∃ H : ℝ, 0≤H ∧ CurvatureBound F H ∧ CurvatureBound (fderiv ℝ F) H := by
  obtain ⟨A,hA⟩ := hF.2 2
  obtain ⟨B,hB⟩ := hF.2 3
  let H := max A 0+max B 0
  have hH : 0≤H := by dsimp [H]; positivity
  refine ⟨2*H,by positivity,curvature_of_second_derivative_bound hF.1 hH ?_,
    curvature_of_second_derivative_bound (hF.1.fderiv_right (by simp)) hH ?_⟩
  · intro x
    exact (hA x).trans (by dsimp [H]; linarith [le_max_left A 0,le_max_right B 0])
  · intro x
    rw [norm_iteratedFDeriv_fderiv]
    exact (hB x).trans (by dsimp [H]; linarith [le_max_left B 0,le_max_right A 0])

lemma CurvatureBound.smul_const {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → ℝ} {H : ℝ} (hf : CurvatureBound f H) (a : W) :
    CurvatureBound (fun x => f x • a) (H*‖a‖) := by
  intro x v
  rw [show f (x+v) • a+f (x-v) • a-(2:ℝ) • (f x • a)=
    (f (x+v)+f (x-v)-(2:ℝ) • f x) • a by simp only [add_smul,sub_smul,smul_smul,smul_eq_mul],norm_smul]
  exact (mul_le_mul_of_nonneg_right (hf x v) (norm_nonneg a)).trans_eq (by ring)

lemma sphere_average_curvature {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Sphere → U → W} {H : ℝ} (hc : ∀ x, Continuous (fun n => f n x))
    (hf : ∀ n, CurvatureBound (f n) H) :
    CurvatureBound (fun x => (4*Real.pi)⁻¹ • ∫ n, f n x ∂sphereMeasure) H := by
  have hh := (CurvatureBound.integral
    (fun x => (hc x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (ae_of_all sphereMeasure hf)).const_smul (4*Real.pi)⁻¹
  simpa only [sphere_area,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹),
    mul_left_comm _ H,inv_mul_cancel₀ (by positivity : 4*Real.pi≠0),mul_one] using hh

lemma uniform_datum_velocity_integral_curvature {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Phase → ℝ} {H : Vec × Vec → W} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ n : Vec, ‖n‖=1 →
      CurvatureBound (fun x => ∫ v : Vec, f (x,v) • H (n,v)) C := by
  obtain ⟨K,hK,hz⟩ := datum_velocity_support hc
  obtain ⟨A,hA,hfa⟩ := smooth_compact_curvature hf hc
  obtain ⟨B,hB⟩ := ((isCompact_sphere (0:Vec) 1).prod hK).exists_bound_of_continuousOn
    (hH.mono (by intro p hp; exact ⟨hp.1,mem_univ _⟩))
  let D := max B 0
  have hD : 0≤D := le_max_right _ _
  refine ⟨(A*D)*(volume K).toReal,by positivity,?_⟩
  intro n hn
  have hn' : n∈sphere (0:Vec) 1 := mem_sphere_zero_iff_norm.mpr hn
  have hint (z : Vec) : Integrable (fun v => f (z,v) • H (n,v)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).smul
        (hH.comp_continuous (continuous_const.prodMk continuous_id) (fun v => ⟨hn',mem_univ v⟩))
    · exact HasCompactSupport.intro hK (fun v hv => by rw [hz z v hv,zero_smul])
  have he (x : Vec) : (∫ v in K, f (x,v) • H (n,v))=∫ v, f (x,v) • H (n,v) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hz x v hv,zero_smul]
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  have hbound : ∀ᵐ v ∂volume.restrict K, CurvatureBound (fun x => f (x,v) • H (n,v)) (A*D) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with v hv
    exact ((hfa.spatial_slice v).smul_const (H (n,v))).mono
      (mul_le_mul_of_nonneg_left ((hB (n,v) ⟨hn',hv⟩).trans (le_max_left _ _)) hA)
  have hh := CurvatureBound.integral (fun x => (hint x).restrict) hbound
  simpa only [he,Measure.real,Measure.restrict_apply_univ] using hh

lemma freeWave_curvature {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (hh : Continuous h)
    {C : ℝ} (hC : 0≤C) (hgc : CurvatureBound g C)
    (hgd : ∀ n : Vec, ‖n‖=1 → CurvatureBound (fun x => fderiv ℝ g x n) C)
    (hhc : CurvatureBound h C) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    CurvatureBound (fun x => freeWave g h (t,x)) (3*C) := by
  have hc (z : Vec) : Continuous (fun n : Sphere => g (z+t • n.1)) :=
    hg.continuous.comp (continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val))
  have hd (z : Vec) : Continuous (fun n : Sphere => fderiv ℝ g (z+t • n.1) n.1) :=
    ((hg.continuous_fderiv (by simp)).comp
      (continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val))).clm_apply continuous_subtype_val
  have hhc' (z : Vec) : Continuous (fun n : Sphere => h (z+t • n.1)) :=
    hh.comp (continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val))
  have A := sphere_average_curvature hc (fun n => hgc.translate (t • n.1))
  have B := (sphere_average_curvature hd (fun n => (hgd n.1 (mem_sphere_zero_iff_norm.mp n.2)).translate (t • n.1))).const_smul t
  have D := (sphere_average_curvature hhc' (fun n => hhc.translate (t • n.1))).const_smul t
  have he : (fun x => freeWave g h (t,x))=(fun x =>
      (4*Real.pi)⁻¹ • (∫ n : Sphere, g (x+t • n.1) ∂sphereMeasure)+
      t • ((4*Real.pi)⁻¹ • (∫ n : Sphere, fderiv ℝ g (x+t • n.1) n.1 ∂sphereMeasure))+
      t • ((4*Real.pi)⁻¹ • (∫ n : Sphere, h (x+t • n.1) ∂sphereMeasure))) := by
    funext x
    rw [freeWave_sphere hg]
    simp only [smul_eq_mul]
    ring
  rw [he]
  exact ((A.add B).add D).mono (by rw [abs_of_nonneg ht.1]; nlinarith [ht.2])

lemma waveK_curvature {g : Vec → ℝ} (hg : Continuous g) {C : ℝ} (hC : 0≤C)
    (hgc : CurvatureBound g C) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    CurvatureBound (fun x => waveK g (t,x)) C := by
  have hc (z : Vec) : Continuous (fun n : Sphere => g (z+t • n.1)) :=
    hg.comp (continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val))
  have hh := (sphere_average_curvature hc (fun n => hgc.translate (t • n.1))).const_smul t
  have he : (fun x => waveK g (t,x))=(fun x => t • ((4*Real.pi)⁻¹ • ∫ n : Sphere, g (x+t • n.1) ∂sphereMeasure)) := by
    funext x
    simp only [waveK,sphereSum,smul_eq_mul]
    ring
  rw [he]
  exact hh.mono (by rw [abs_of_nonneg ht.1]; exact mul_le_of_le_one_left hC ht.2)

lemma CurvatureBound.curl_coordinate {F : Vec → Vec} {H : ℝ}
    (hF : Differentiable ℝ F) (hc : CurvatureBound (fderiv ℝ F) H) (i : Fin 3) :
    CurvatureBound (fun x => curl F x i) (2*H) := by
  have ha (j : Fin 3) : CurvatureBound (fun x => fderiv ℝ F x (basis j)) H := by
    simpa [basis,PiLp.norm_single] using hc.clm_apply_const (basis j)
  have he : (fun x => curl F x i)=(fun x => (fderiv ℝ F x (basis (curlA i))) (curlB i)-
      (fderiv ℝ F x (basis (curlB i))) (curlA i)) := by
    funext x
    fin_cases i <;> simp [curl,curlA,curlB,spatialPartial,coordinate_fderiv_apply hF]
  rw [he]
  convert ((ha (curlA i)).coordinate (curlB i)).sub ((ha (curlB i)).coordinate (curlA i)) using 1
  ring

lemma BoundedSmooth.freeWave_coordinate_curvature {E B : Vec → Vec}
    (hE : BoundedSmooth E) (hB : BoundedSmooth B) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) 1,
      CurvatureBound (fun x => freeWave (fun z => E z i) (fun z => curl B z i) (t,x)) C ∧
      CurvatureBound (fun x => freeWave (fun z => B z i) (fun z => -curl E z i) (t,x)) C := by
  obtain ⟨A,hA,hEc,hEdc⟩ := hE.spatial_curvature
  obtain ⟨D,hD,hBc,hBdc⟩ := hB.spatial_curvature
  let C := 2*(A+D)
  have hC : 0≤C := by dsimp [C]; positivity
  have hAC : A≤C := by dsimp [C]; linarith
  have hDC : D≤C := by dsimp [C]; linarith
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  refine ⟨3*C,by positivity,?_⟩
  intro t ht
  constructor
  · apply freeWave_curvature (hproj.comp hE.1)
      (hproj.continuous.comp (contDiff_curl hB.1).continuous) hC ((hEc.coordinate i).mono hAC) _
      ((hBdc.curl_coordinate (hB.1.differentiable (by simp)) i).mono (by dsimp [C]; linarith)) ht
    intro n hn
    have hh := ((hEdc.clm_apply_const n).coordinate i).mono (show A*‖n‖≤C by rw [hn,mul_one]; exact hAC)
    simpa only [Function.comp_def,coordinate_fderiv_apply (hE.1.differentiable (by simp))] using hh
  · apply freeWave_curvature (hproj.comp hB.1)
      (hproj.continuous.comp (contDiff_curl hE.1).continuous).neg hC ((hBc.coordinate i).mono hDC) _
      (((hEdc.curl_coordinate (hE.1.differentiable (by simp)) i).mono (by dsimp [C]; linarith)).neg) ht
    intro n hn
    have hh := ((hBdc.clm_apply_const n).coordinate i).mono (show D*‖n‖≤C by rw [hn,mul_one]; exact hDC)
    simpa only [Function.comp_def,coordinate_fderiv_apply (hB.1.differentiable (by simp))] using hh

lemma CurvatureBound.dot_const {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {f : U → Vec} {H : ℝ} (hf : CurvatureBound f H) (n : Vec) :
    CurvatureBound (fun x => dot n (f x)) (‖n‖*H) := by
  intro x v
  change |dot n (f (x+v))+dot n (f (x-v))-2*dot n (f x)|≤_
  rw [← dot_add_right,← dot_smul_right,← dot_sub_right]
  exact (abs_dot_le _ _).trans ((mul_le_mul_of_nonneg_left (hf x v) (norm_nonneg _)).trans_eq (by ring))

lemma datum_moment_curvature {d : Datum} (hd : Admissible d) :
    ∃ H : ℝ, 0≤H ∧ CurvatureBound (rho d.f₀) H ∧ CurvatureBound (current d.f₀) H := by
  obtain ⟨A,hA,ha⟩ := uniform_datum_velocity_integral_curvature
    hd.1 hd.2.1 (H:=fun _ => (1:ℝ)) continuousOn_const
  obtain ⟨B,hB,hb⟩ := uniform_datum_velocity_integral_curvature
    hd.1 hd.2.1 (((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousOn)
  refine ⟨A+B,add_nonneg hA hB,?_,?_⟩
  · have hh := (ha (basis 0) (by simp [basis,PiLp.norm_single])).mono (le_add_of_nonneg_right hB)
    change CurvatureBound (fun x => ∫ v : Vec, d.f₀ (x,v)) (A+B)
    simpa only [smul_eq_mul,mul_one] using hh
  · exact (hb (basis 0) (by simp [basis,PiLp.norm_single])).mono (le_add_of_nonneg_left hA)

lemma datum_sphere_flux_curvature {f : Phase → ℝ} {H : Vec × Vec → Vec}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) 1,
      CurvatureBound (fun x => (4*Real.pi)⁻¹*(∫ n : Sphere,
        t*dot n.1 (∫ v, f (x+t • n.1,v) • H (-n.1,v)) ∂sphereMeasure)) C := by
  obtain ⟨C,hC,hb⟩ := uniform_datum_velocity_integral_curvature hf hc hH
  refine ⟨C,hC,?_⟩
  intro t ht
  have hn (n : Sphere) : ‖n.1‖=1 := mem_sphere_zero_iff_norm.mp n.2
  have hc' (z : Vec) : Continuous (fun n : Sphere =>
      t*dot n.1 (∫ v, f (z+t • n.1,v) • H (-n.1,v))) := by
    have hI : Continuous (fun n : Sphere => ∫ v, f (z+t • n.1,v) • H (-n.1,v)) := by
      apply (continuousOn_datum_velocity_integral hf.continuous hc hH).comp_continuous
        ((continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val)).prodMk continuous_subtype_val.neg)
      intro n
      exact ⟨mem_univ _,by simpa only [mem_sphere_zero_iff_norm,Pi.neg_apply,norm_neg] using hn n⟩
    exact continuous_const.mul ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_subtype_val.prodMk hI))
  apply sphere_average_curvature hc'
  intro n
  have hh := (((hb (-n.1) (by rw [norm_neg,hn n])).translate (t • n.1)).dot_const n.1).const_smul t
  apply hh.mono
  rw [hn n,one_mul,abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left hC ht.2

lemma weighted_sphere_mean_curvature {g : Vec → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : 0≤C) (h : CurvatureBound g C)
    {w : Sphere → ℝ} (hw : Continuous w) (hwb : ∀ n, |w n|≤1)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    CurvatureBound (fun x => (4*Real.pi)⁻¹*(∫ n : Sphere, t*w n*g (x+t • n.1) ∂sphereMeasure)) C := by
  have hc (z : Vec) : Continuous (fun n : Sphere => t*w n*g (z+t • n.1)) :=
    (continuous_const.mul hw).mul (hg.comp (continuous_const.add
      ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val)))
  apply sphere_average_curvature hc
  intro n
  apply ((h.translate (t • n.1)).const_smul (t*w n)).mono
  rw [abs_mul,abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left hC ((mul_le_mul_of_nonneg_left (hwb n) ht.1).trans (by simpa only [mul_one] using ht.2))

lemma electricConeBoundary_datum_curvature {d : Datum} (hd : Admissible d) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) 1,
      CurvatureBound (fun x => electricConeBoundary (datumBoundarySolution d) t x i 0) C := by
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_curvature hd.2.2.2.1 hd.2.2.2.2.1 i
  obtain ⟨B,hB,hflux⟩ := datum_sphere_flux_curvature hd.1 hd.2.1 (continuousOn_datumElectricFluxKernel i)
  obtain ⟨D,hD,hrc,hjc⟩ := datum_moment_curvature hd
  obtain ⟨M,hM,hmom⟩ := datum_moment_lipschitz hd
  have hm : Continuous (rho d.f₀) ∧ Continuous (current d.f₀) := by
    constructor
    · exact (LipschitzWith.of_dist_le' (K:=M) (fun x y => by
        simpa only [dist_eq_norm,Real.norm_eq_abs] using (hmom y x).1)).continuous
    · exact (LipschitzWith.of_dist_le' (K:=M) (fun x y => by
        simpa only [dist_eq_norm] using (hmom y x).2)).continuous
  have hproj : Continuous (fun v : Vec => v i) := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous
  refine ⟨A+B+2*D,by positivity,?_⟩
  intro t ht
  have hrho := weighted_sphere_mean_curvature hm.1 hD hrc
    (hproj.comp continuous_subtype_val) (fun n => (norm_coordinate_le n.1 i).trans_eq (mem_sphere_zero_iff_norm.mp n.2))
    ⟨ht.1.le,ht.2⟩
  have hj := waveK_curvature (hproj.comp hm.2) hD (hjc.coordinate i) ⟨ht.1.le,ht.2⟩
  have hh := ((((hfree t ⟨ht.1.le,ht.2⟩).1).sub (hflux t ⟨ht.1.le,ht.2⟩)).sub hrho).sub hj
  have he : A+B+D+D=A+B+2*D := by ring
  rw [he] at hh
  simp only [electricConeBoundary,sub_zero]
  simp_rw [datum_initial_electric_flux_normalised d i ht.1]
  simpa only [datumBoundarySolution,Function.comp_def] using hh

lemma magneticConeBoundary_datum_curvature {d : Datum} (hd : Admissible d) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) 1,
      CurvatureBound (fun x => magneticConeBoundary (datumBoundarySolution d) t x i 0) C := by
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_curvature hd.2.2.2.1 hd.2.2.2.2.1 i
  obtain ⟨B,hB,hflux⟩ := datum_sphere_flux_curvature hd.1 hd.2.1 (continuousOn_datumMagneticFluxKernel i)
  obtain ⟨D,hD,hrc,hjc⟩ := datum_moment_curvature hd
  obtain ⟨M,hM,hmom⟩ := datum_moment_lipschitz hd
  have hm : Continuous (current d.f₀) := (LipschitzWith.of_dist_le' (K:=M) (fun x y => by
    simpa only [dist_eq_norm] using (hmom y x).2)).continuous
  have hproj (j : Fin 3) : Continuous (fun v : Vec => v j) := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous
  refine ⟨A+B+2*D,by positivity,?_⟩
  intro t ht
  let F : Fin 3 → Fin 3 → Vec → Sphere → ℝ := fun j k x n => t*n.1 j*current d.f₀ (x+t • n.1) k
  have hfc (j k : Fin 3) (x : Vec) : Continuous (F j k x) :=
    (continuous_const.mul ((hproj j).comp continuous_subtype_val)).mul
      (((hproj k).comp hm).comp (continuous_const.add
        ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val)))
  have hc (j k : Fin 3) : CurvatureBound (fun x => (4*Real.pi)⁻¹*(∫ n : Sphere, F j k x n ∂sphereMeasure)) D :=
    weighted_sphere_mean_curvature ((hproj k).comp hm) hD (hjc.coordinate k)
      ((hproj j).comp continuous_subtype_val) (fun n => (norm_coordinate_le n.1 j).trans_eq (mem_sphere_zero_iff_norm.mp n.2))
      ⟨ht.1.le,ht.2⟩
  have hj := (hc (curlA i) (curlB i)).sub (hc (curlB i) (curlA i))
  have hje : (fun x => (4*Real.pi)⁻¹*(∫ n : Sphere, F (curlA i) (curlB i) x n ∂sphereMeasure)-
      (4*Real.pi)⁻¹*(∫ n : Sphere, F (curlB i) (curlA i) x n ∂sphereMeasure))=
      (fun x => (4*Real.pi)⁻¹*(∫ n : Sphere,
        F (curlA i) (curlB i) x n-F (curlB i) (curlA i) x n ∂sphereMeasure)) := by
    funext x
    rw [integral_sub ((hfc _ _ x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((hfc _ _ x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),mul_sub]
  rw [hje] at hj
  have hh := (((hfree t ⟨ht.1.le,ht.2⟩).2).sub (hflux t ⟨ht.1.le,ht.2⟩)).add hj
  rw [show (A+B)+(D+D)=A+B+2*D by ring] at hh
  simp only [magneticConeBoundary,sub_zero]
  simp_rw [datum_initial_magnetic_flux_normalised d i ht.1]
  simpa only [datumBoundarySolution,F,Function.comp_def] using hh

lemma datum_boundary_global_curvature {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ, 0≤C ∧ CurvatureBound d.E₀ C ∧ CurvatureBound d.B₀ C ∧
      ∀ t∈Ioc (0:ℝ) 1,
        CurvatureBound (fun x => electricBoundaryField (datumBoundarySolution d) t x) C ∧
        CurvatureBound (fun x => magneticBoundaryField (datumBoundarySolution d) t x) C := by
  obtain ⟨E,hE,hEc,_⟩ := hd.2.2.2.1.spatial_curvature
  obtain ⟨B,hB,hBc,_⟩ := hd.2.2.2.2.1.spatial_curvature
  choose CE hCE he using electricConeBoundary_datum_curvature hd
  choose CB hCB hb using magneticConeBoundary_datum_curvature hd
  let S := E+B+∑ i : Fin 3, (CE i+CB i)
  have hS : 0≤S := by dsimp [S]; exact add_nonneg (add_nonneg hE hB) (Finset.sum_nonneg fun i _ => add_nonneg (hCE i) (hCB i))
  have hsum : 0≤∑ i : Fin 3, (CE i+CB i) := Finset.sum_nonneg fun i _ => add_nonneg (hCE i) (hCB i)
  have hEC (i : Fin 3) : CE i≤S := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [S]; linarith [hCB i]
  have hBC (i : Fin 3) : CB i≤S := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [S]; linarith [hCE i]
  refine ⟨3*S,by positivity,hEc.mono (by dsimp [S]; linarith),hBc.mono (by dsimp [S]; linarith),?_⟩
  intro t ht
  constructor
  · intro x v
    have hh := norm_le_three_of_coordinate_bound (mul_nonneg hS (sq_nonneg ‖v‖))
      (v:=electricBoundaryField (datumBoundarySolution d) t (x+v)+
        electricBoundaryField (datumBoundarySolution d) t (x-v)-
        (2:ℝ) • electricBoundaryField (datumBoundarySolution d) t x)
      (fun i => (he i t ht x v).trans (mul_le_mul_of_nonneg_right (hEC i) (sq_nonneg _)))
    exact hh.trans_eq (by ring)
  · intro x v
    have hh := norm_le_three_of_coordinate_bound (mul_nonneg hS (sq_nonneg ‖v‖))
      (v:=magneticBoundaryField (datumBoundarySolution d) t (x+v)+
        magneticBoundaryField (datumBoundarySolution d) t (x-v)-
        (2:ℝ) • magneticBoundaryField (datumBoundarySolution d) t x)
      (fun i => (hb i t ht x v).trans (mul_le_mul_of_nonneg_right (hBC i) (sq_nonneg _)))
    exact hh.trans_eq (by ring)

end

section

open Set Filter MeasureTheory
open scoped Topology

lemma variable_integral_gronwall_bound {f b : ℝ → ℝ} (hf : Continuous f)
    (hb : Continuous b) {a T : ℝ} (hb0 : ∀ t∈Icc (0:ℝ) T,0≤b t)
    (hbound : ∀ t∈Icc (0:ℝ) T,f t≤a+∫ r in 0..t,b r*f r) :
    ∀ t∈Icc (0:ℝ) T,f t≤a*Real.exp (∫ r in 0..t,b r) := by
  let G : ℝ → ℝ := fun t => a+∫ r in 0..t,b r*f r
  let B : ℝ → ℝ := fun t => ∫ r in 0..t,b r
  have hG : Continuous G := continuous_const.add
    (intervalIntegral.continuous_primitive (hb.mul hf).intervalIntegrable 0)
  have hB : Continuous B := intervalIntegral.continuous_primitive hb.intervalIntegrable 0
  have hdG (t : ℝ) : HasDerivAt G (b t*f t) t := by
    exact (intervalIntegral.integral_hasDerivAt_right ((hb.mul hf).intervalIntegrable 0 t)
      (hb.mul hf).stronglyMeasurable.stronglyMeasurableAtFilter (hb.mul hf).continuousAt).const_add a
  have hdB (t : ℝ) : HasDerivAt B (b t) t :=
    intervalIntegral.integral_hasDerivAt_right (hb.intervalIntegrable 0 t)
      hb.stronglyMeasurable.stronglyMeasurableAtFilter hb.continuousAt
  let H : ℝ → ℝ := fun t => Real.exp (-B t)*G t
  have hdH (t : ℝ) : HasDerivAt H
      (Real.exp (-B t)*(b t*f t-b t*G t)) t := by
    have hd := ((hdB t).neg.exp.mul (hdG t))
    change HasDerivAt H ((Real.exp (-B t))*(-b t)*G t+Real.exp (-B t)*(b t*f t)) t at hd
    convert hd using 1
    ring
  have hmono : AntitoneOn H (Icc (0:ℝ) T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (((Real.continuous_exp.comp hB.neg).mul hG).continuousOn) (fun t ht => (hdH t).differentiableAt.differentiableWithinAt)
    intro t ht
    change deriv H t ≤ 0
    rw [(hdH t).deriv]
    have ht' : t∈Icc (0:ℝ) T := interior_subset ht
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left (hbound t ht') (hb0 t ht'))
  intro t ht
  have hh := hmono (show (0:ℝ)∈Icc 0 T from ⟨le_rfl,ht.1.trans ht.2⟩) ht ht.1
  have hh' : Real.exp (-B t)*G t≤a := by
    simpa only [H,G,B,intervalIntegral.integral_same,add_zero,neg_zero,Real.exp_zero,one_mul] using hh
  have hs := mul_le_mul_of_nonneg_left hh' (Real.exp_pos (B t)).le
  have he : Real.exp (B t)*(Real.exp (-B t)*G t)=G t := by
    rw [←mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]
  rw [he] at hs
  exact (hbound t ht).trans (by simpa only [G,B,mul_comm] using hs)

lemma variable_integral_gronwall_bound_on {f b : ℝ → ℝ} {a T : ℝ} (hT : 0≤T)
    (hf : ContinuousOn f (Icc (0:ℝ) T)) (hb : ContinuousOn b (Icc (0:ℝ) T))
    (hb0 : ∀ t∈Icc (0:ℝ) T,0≤b t)
    (hbound : ∀ t∈Icc (0:ℝ) T,f t≤a+∫ r in 0..t,b r*f r) :
    ∀ t∈Icc (0:ℝ) T,f t≤a*Real.exp (∫ r in 0..t,b r) := by
  let p : ℝ → ℝ := fun r => max 0 (min T r)
  have hp : ∀ r, p r∈Icc (0:ℝ) T := fun r =>
    ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩
  have he (r : ℝ) (hr : r∈Icc (0:ℝ) T) : p r=r := by
    dsimp [p]; rw [min_eq_right hr.2,max_eq_right hr.1]
  have hcp : Continuous p := by fun_prop
  have hh := variable_integral_gronwall_bound
    (hf.comp_continuous hcp hp) (hb.comp_continuous hcp hp)
    (fun r hr => hb0 (p r) (hp r)) (a:=a) (T:=T) (fun r hr => by
      simpa only [Function.comp_apply,he r hr] using (hbound r hr).trans_eq
        (congrArg (a+·) (intervalIntegral.integral_congr (fun u hu => by
          have hu' : u∈Icc (0:ℝ) T := ⟨(uIcc_of_le hr.1 ▸ hu).1,(uIcc_of_le hr.1 ▸ hu).2.trans hr.2⟩
          simp only [he u hu']))))
  intro t ht
  have hi : (∫ r in 0..t,(b ∘ p) r)=∫ r in 0..t,b r :=
    intervalIntegral.integral_congr (fun r hr => by
      have hr' : r∈Icc (0:ℝ) T := ⟨(uIcc_of_le ht.1 ▸ hr).1,(uIcc_of_le ht.1 ▸ hr).2.trans ht.2⟩
      simp only [Function.comp_apply,he r hr'])
  have hout := hh t ht
  rw [hi] at hout
  simpa only [Function.comp_apply,he t ht] using hout

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma norm_ode_volterra_bound {z dz : ℝ → E} {b : ℝ → ℝ} {T : ℝ} (hT : 0≤T)
    (hz : ContinuousOn z (Icc (0:ℝ) T)) (hdz : ContinuousOn dz (Icc (0:ℝ) T))
    (hb : ContinuousOn b (Icc (0:ℝ) T)) (hb0 : ∀ r∈Icc (0:ℝ) T,0≤b r)
    (hder : ∀ r∈Ioo (0:ℝ) T,HasDerivAt z (dz r) r)
    (hbound : ∀ r∈Icc (0:ℝ) T,‖dz r‖≤b r*‖z r‖) :
    ∀ t∈Icc (0:ℝ) T,‖z t‖≤‖z 0‖*Real.exp (∫ r in 0..t,b r) := by
  apply variable_integral_gronwall_bound_on hT hz.norm hb hb0
  intro t ht
  have hsub : Icc (0:ℝ) t ⊆ Icc (0:ℝ) T := fun r hr => ⟨hr.1,hr.2.trans ht.2⟩
  have hi : IntervalIntegrable dz volume 0 t := (hdz.mono hsub).intervalIntegrable_of_Icc ht.1
  have he : ∫ r in 0..t,dz r=z t-z 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hz.mono hsub)
      (fun r hr => hder r ⟨hr.1,hr.2.trans_le ht.2⟩) hi
  calc
    ‖z t‖ = ‖z 0+∫ r in 0..t,dz r‖ := by rw [he]; congr 1; abel
    _ ≤ ‖z 0‖+∫ r in 0..t,‖dz r‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm ht.1))
    _ ≤ ‖z 0‖+∫ r in 0..t,b r*‖z r‖ := by
      apply add_le_add le_rfl
      apply intervalIntegral.integral_mono_on ht.1 hi.norm
        (((hb.mul hz.norm).mono hsub).intervalIntegrable_of_Icc ht.1)
      exact fun r hr => hbound r (hsub hr)

lemma backward_norm_ode_volterra_bound {z dz : ℝ → E} {b : ℝ → ℝ} {T : ℝ} (hT : 0≤T)
    (hz : ContinuousOn z (Icc (0:ℝ) T)) (hdz : ContinuousOn dz (Icc (0:ℝ) T))
    (hb : ContinuousOn b (Icc (0:ℝ) T)) (hb0 : ∀ r∈Icc (0:ℝ) T,0≤b r)
    (hder : ∀ r∈Ioo (0:ℝ) T,HasDerivAt z (dz r) r)
    (hbound : ∀ r∈Icc (0:ℝ) T,‖dz r‖≤b r*‖z r‖) :
    ‖z 0‖≤‖z T‖*Real.exp (∫ r in 0..T,b r) := by
  have hm : MapsTo (fun r:ℝ => T-r) (Icc (0:ℝ) T) (Icc (0:ℝ) T) :=
    fun r hr => ⟨sub_nonneg.mpr hr.2,sub_le_self _ hr.1⟩
  have hc : Continuous (fun r:ℝ => T-r) := continuous_const.sub continuous_id
  have he (r : ℝ) (hr : r∈Ioo (0:ℝ) T) :
      HasDerivAt (fun u => z (T-u)) (-dz (T-r)) r := by
    have hd := (hder (T-r) ⟨by linarith [hr.2],by linarith [hr.1]⟩).scomp r
      ((hasDerivAt_id r).const_sub T)
    simpa only [one_smul,neg_smul,Function.comp_def] using hd
  have hh := norm_ode_volterra_bound hT (hz.comp hc.continuousOn hm)
    (hdz.neg.comp hc.continuousOn hm) (hb.comp hc.continuousOn hm)
    (fun r hr => hb0 (T-r) (hm hr)) he (fun r hr => by
      simpa only [Function.comp_apply,Pi.neg_apply,norm_neg] using hbound (T-r) (hm hr)) T ⟨hT,le_rfl⟩
  simpa only [Function.comp_apply,sub_self, sub_zero, intervalIntegral.integral_comp_sub_left] using hh

end


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

section

lemma transport_on_characteristic_before {s : Solution} {X V : ℝ → Vec} {T U : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (heq : EquationsBefore s U)
    (hT : 0≤T) (hTU : T≤U)
    (hXc : ContinuousOn X (Icc 0 T)) (hVc : ContinuousOn V (Icc 0 T))
    (hX : ∀ t∈Ioo 0 T,HasDerivAt X (velocity (V t)) t)
    (hV : ∀ t∈Ioo 0 T,HasDerivAt V (s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))) t) :
    s.f (T,X T,V T)=s.f (0,X 0,V 0) := by
  rcases hT.eq_or_lt with h|h
  · simp [←h]
  have hc : ContinuousOn (fun t => s.f (t,X t,V t)) (Icc 0 T) :=
    hf.continuousOn.comp (continuousOn_id.prodMk (hXc.prodMk hVc)) (fun t ht => ht.1)
  have hd : ∀ t∈Ioo 0 T,HasDerivAt (fun r => s.f (r,X r,V r)) (0:ℝ) t := by
    intro t ht
    have hder := hasDerivAt_particle_along_curve
      (particle_differentiableAt_positive hf ht.1 (X t) (V t)) (hX t ht) (hV t ht)
    have hpde := (heq t ht.1.le (ht.2.trans_le hTU)).1 (X t) (V t)
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hpde
    exact hpde ▸ hder
  obtain ⟨r,hr,he⟩ := exists_hasDerivAt_eq_slope (fun r => s.f (r,X r,V r)) (fun _ => 0) h hc hd
  exact sub_eq_zero.mp ((div_eq_zero_iff.mp he.symm).resolve_right (sub_ne_zero.mpr (ne_of_gt h)))

lemma continuousOn_lorentz_along {E B : Field} {α : ℝ → Phase} {T : ℝ}
    (hE : ContDiffOn ℝ 1 E fieldHalfSpace) (hB : ContDiffOn ℝ 1 B fieldHalfSpace)
    (hα : ContinuousOn α (Icc (0:ℝ) T)) :
    ContinuousOn (fun r => lorentzField E B (r,α r)) (Icc (0:ℝ) T) := by
  have hx : ContinuousOn (fun r => (r,(α r).1)) (Icc (0:ℝ) T) := continuousOn_id.prodMk hα.fst
  have hm : MapsTo (fun r => (r,(α r).1)) (Icc (0:ℝ) T) fieldHalfSpace := fun r hr => hr.1
  have hu : ContinuousOn (fun r => velocity (α r).2) (Icc (0:ℝ) T) :=
    (contDiff_velocity (k:=1)).continuous.comp_continuousOn hα.snd
  exact hu.prodMk ((hE.continuousOn.comp hx hm).add
    ((contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.prodMk (hB.continuousOn.comp hx hm))))

lemma characteristic_separation_volterra {E B : Field} {α γ : ℝ → Phase} {T L : ℝ}
    {g : ℝ → ℝ} (hT : 0≤T) (hL : 0≤L)
    (hE : ContDiffOn ℝ 1 E fieldHalfSpace) (hB : ContDiffOn ℝ 1 B fieldHalfSpace)
    (hα : ContinuousOn α (Icc (0:ℝ) T)) (hγ : ContinuousOn γ (Icc (0:ℝ) T))
    (hdα : ∀ r∈Ioo (0:ℝ) T,HasDerivAt α (lorentzField E B (r,α r)) r)
    (hdγ : ∀ r∈Ioo (0:ℝ) T,HasDerivAt γ (lorentzField E B (r,γ r)) r)
    (hg : ContinuousOn g (Icc (0:ℝ) T)) (hg0 : ∀ r∈Icc (0:ℝ) T,0≤g r)
    (hBb : ∀ r∈Icc (0:ℝ) T,∀ x,‖B (r,x)‖≤L)
    (hEx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖E (r,y)-E (r,x)‖≤g r*‖y-x‖)
    (hBx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖B (r,y)-B (r,x)‖≤g r*‖y-x‖) :
    ‖α 0-γ 0‖≤‖α T-γ T‖*Real.exp (∫ r in 0..T,1+2*g r+L) := by
  apply backward_norm_ode_volterra_bound hT (hα.sub hγ)
    ((continuousOn_lorentz_along hE hB hα).sub (continuousOn_lorentz_along hE hB hγ))
    ((continuousOn_const.add (continuousOn_const.mul hg)).add continuousOn_const)
    (fun r hr => by change 0≤1+2*g r+L; linarith [hg0 r hr]) (fun r hr => (hdα r hr).sub (hdγ r hr))
  intro r hr
  change ‖lorentzField E B (r,α r)-lorentzField E B (r,γ r)‖≤(1+2*g r+L)*‖α r-γ r‖
  simpa only [mul_zero,add_zero] using lorentzField_difference_bound hL (hg0 r hr)
    (D:=0) le_rfl (hBb r hr) (hEx r hr) (hBx r hr) (by intros; simp) (by intros; simp) (α r) (γ r)

lemma particle_lipschitz_volterra_before {d : Datum} {s : Solution} {T U A L : ℝ}
    {g : ℝ → ℝ} (hs : ClassicalBefore d s U) (hT : 0≤T) (hTU : T≤U)
    (hA : 0≤A) (hL : 0≤L)
    (h₀ : ∀ z w,|d.f₀ z-d.f₀ w|≤A*‖z-w‖)
    (hg : ContinuousOn g (Icc (0:ℝ) T)) (hg0 : ∀ r∈Icc (0:ℝ) T,0≤g r)
    (hBb : ∀ r∈Icc (0:ℝ) T,∀ x,‖s.B (r,x)‖≤L)
    (hEx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖s.E (r,y)-s.E (r,x)‖≤g r*‖y-x‖)
    (hBx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖s.B (r,y)-s.B (r,x)‖≤g r*‖y-x‖)
    (z w : Phase) :
    |s.f (T,z)-s.f (T,w)|≤(A*Real.exp (∫ r in 0..T,1+2*g r+L))*‖z-w‖ := by
  obtain ⟨X,V,hXT,hVT,hX,hV,_⟩ := exists_characteristic_on_slab hT ⟨hT,le_rfl⟩ hs.2.1 hs.2.2.1 z.1 z.2
  obtain ⟨Y,W,hYT,hWT,hY,hW,_⟩ := exists_characteristic_on_slab hT ⟨hT,le_rfl⟩ hs.2.1 hs.2.2.1 w.1 w.2
  have hXc : ContinuousOn X (Icc 0 T) := fun r hr => (hX r hr).continuousWithinAt
  have hVc : ContinuousOn V (Icc 0 T) := fun r hr => (hV r hr).continuousWithinAt
  have hYc : ContinuousOn Y (Icc 0 T) := fun r hr => (hY r hr).continuousWithinAt
  have hWc : ContinuousOn W (Icc 0 T) := fun r hr => (hW r hr).continuousWithinAt
  have hdX := fun r hr => (hX r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have hdV := fun r hr => (hV r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have hdY := fun r hr => (hY r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have hdW := fun r hr => (hW r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have hf := transport_on_characteristic_before hs.1 hs.2.2.2.2.2.2.2.1 hT hTU hXc hVc hdX hdV
  have hf' := transport_on_characteristic_before hs.1 hs.2.2.2.2.2.2.2.1 hT hTU hYc hWc hdY hdW
  rw [hXT,hVT,hs.2.2.2.2.2.2.2.2.1] at hf
  rw [hYT,hWT,hs.2.2.2.2.2.2.2.2.1] at hf'
  have hsep := characteristic_separation_volterra hT hL hs.2.1 hs.2.2.1 (hXc.prodMk hVc) (hYc.prodMk hWc)
    (fun r hr => (hdX r hr).prodMk (hdV r hr)) (fun r hr => (hdY r hr).prodMk (hdW r hr)) hg hg0 hBb hEx hBx
  simp only [hXT,hVT,hYT,hWT,Prod.mk.eta] at hsep
  change |s.f (T,z.1,z.2)-s.f (T,w.1,w.2)|≤_
  rw [hf,hf']
  exact (h₀ (X 0,V 0) (Y 0,W 0)).trans ((mul_le_mul_of_nonneg_left hsep hA).trans_eq (by ring))

lemma admissible_particle_lipschitz {d : Datum} (hd : Admissible d) :
    ∃ A : ℝ, 0≤A ∧ ∀ z w, |d.f₀ z-d.f₀ w|≤A*‖z-w‖ := by
  obtain ⟨A,hA⟩ := (hd.1.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hd.2.1.fderiv ℝ)
  refine ⟨max A 0,le_max_right _ _,?_⟩
  intro z w
  have hh := (convex_univ : Convex ℝ (univ : Set Phase)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hd.1.differentiable (by simp) z) (C:=max A 0)
    (fun z _ => (hA z).trans (le_max_left A 0)) (mem_univ w) (mem_univ z)
  simpa only [Real.norm_eq_abs] using hh

lemma particle_gradient_volterra_before {d : Datum} {s : Solution} {T U A L : ℝ}
    {g : ℝ → ℝ} (hs : ClassicalBefore d s U) (hT : 0≤T) (hTU : T≤U)
    (hA : 0≤A) (hL : 0≤L)
    (h₀ : ∀ z w,|d.f₀ z-d.f₀ w|≤A*‖z-w‖)
    (hg : ContinuousOn g (Icc (0:ℝ) T)) (hg0 : ∀ r∈Icc (0:ℝ) T,0≤g r)
    (hBb : ∀ r∈Icc (0:ℝ) T,∀ x,‖s.B (r,x)‖≤L)
    (hEx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖s.E (r,y)-s.E (r,x)‖≤g r*‖y-x‖)
    (hBx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖s.B (r,y)-s.B (r,x)‖≤g r*‖y-x‖) :
    ∀ t∈Icc (0:ℝ) T,∀ y v,
      ‖fderiv ℝ (fun z => s.f (t,z,v)) y‖≤A*Real.exp (∫ r in 0..T,1+2*g r+L) := by
  intro t ht y v
  have hsub : Icc (0:ℝ) t ⊆ Icc (0:ℝ) T := fun r hr => ⟨hr.1,hr.2.trans ht.2⟩
  have hβ : ContinuousOn (fun r => 1+2*g r+L) (Icc (0:ℝ) T) := by fun_prop
  have hI : (∫ r in 0..t,1+2*g r+L)≤∫ r in 0..T,1+2*g r+L := by
    apply intervalIntegral.integral_mono_interval (μ:=volume) le_rfl ht.1 ht.2 _ (hβ.intervalIntegrable_of_Icc hT)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    change 0≤1+2*g r+L
    linarith [hg0 r ⟨hr.1.le,hr.2⟩]
  let N := A*Real.exp (∫ r in 0..T,1+2*g r+L)
  have hN : 0≤N := mul_nonneg hA (Real.exp_pos _).le
  have hLip : LipschitzWith ⟨N,hN⟩ (fun z => s.f (t,z,v)) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    have hh := particle_lipschitz_volterra_before hs ht.1 (ht.2.trans hTU) hA hL h₀
      (hg.mono hsub) (fun r hr => hg0 r (hsub hr))
      (fun r hr => hBb r (hsub hr)) (fun r hr => hEx r (hsub hr)) (fun r hr => hBx r (hsub hr)) (a,v) (b,v)
    have hnorm : ‖(a,v)-(b,v)‖=‖a-b‖ := by simp [Prod.norm_def]
    rw [hnorm] at hh
    change ‖s.f (t,a,v)-s.f (t,b,v)‖≤N*‖a-b‖
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hI) hA) (norm_nonneg _))
  exact norm_fderiv_le_of_lipschitz ℝ hLip

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma norm_ode_inhomogeneous_bound {z dz : ℝ → E} {c : ℝ → ℝ} {T K : ℝ}
    (hT : 0≤T) (hK : 0≤K)
    (hz : ContinuousOn z (Icc (0:ℝ) T)) (hdz : ContinuousOn dz (Icc (0:ℝ) T))
    (hc : ContinuousOn c (Icc (0:ℝ) T)) (hc0 : ∀ r∈Icc (0:ℝ) T,0≤c r)
    (hder : ∀ r∈Ioo (0:ℝ) T,HasDerivAt z (dz r) r)
    (hbound : ∀ r∈Icc (0:ℝ) T,‖dz r‖≤K*‖z r‖+c r) :
    ∀ t∈Icc (0:ℝ) T,‖z t‖≤(‖z 0‖+∫ r in 0..T,c r)*Real.exp (K*t) := by
  have hb : ∀ t∈Icc (0:ℝ) T,‖z t‖≤(‖z 0‖+∫ r in 0..T,c r)+∫ r in 0..t,K*‖z r‖ := by
    intro t ht
    have hsub : Icc (0:ℝ) t ⊆ Icc (0:ℝ) T := fun r hr => ⟨hr.1,hr.2.trans ht.2⟩
    have hi : IntervalIntegrable dz volume 0 t := (hdz.mono hsub).intervalIntegrable_of_Icc ht.1
    have he : ∫ r in 0..t,dz r=z t-z 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hz.mono hsub)
        (fun r hr => hder r ⟨hr.1,hr.2.trans_le ht.2⟩) hi
    have hci : IntervalIntegrable c volume 0 t := (hc.mono hsub).intervalIntegrable_of_Icc ht.1
    have hki : IntervalIntegrable (fun r => K*‖z r‖) volume 0 t := ((continuousOn_const.mul hz.norm).mono hsub).intervalIntegrable_of_Icc ht.1
    have hcle : (∫ r in 0..t,c r)≤∫ r in 0..T,c r := by
      apply intervalIntegral.integral_mono_interval (μ:=volume) le_rfl ht.1 ht.2 _
        (hc.intervalIntegrable_of_Icc hT)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hc0 r ⟨hr.1.le,hr.2⟩
    calc
      ‖z t‖ = ‖z 0+∫ r in 0..t,dz r‖ := by rw [he]; congr 1; abel
      _ ≤ ‖z 0‖+∫ r in 0..t,‖dz r‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm ht.1))
      _ ≤ ‖z 0‖+∫ r in 0..t,K*‖z r‖+c r := by
        apply add_le_add le_rfl
        exact intervalIntegral.integral_mono_on ht.1 hi.norm (hki.add hci) (fun r hr => hbound r (hsub hr))
      _ ≤ _ := by rw [intervalIntegral.integral_add hki hci]; linarith
  have hh := variable_integral_gronwall_bound_on hT hz.norm continuousOn_const (fun _ _ => hK) hb
  intro t ht
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm t K] using hh t ht

lemma backward_norm_ode_uniform_bound {z dz : ℝ → E} {T K : ℝ}
    (hT : 0≤T) (hK : 0≤K)
    (hz : ContinuousOn z (Icc (0:ℝ) T)) (hdz : ContinuousOn dz (Icc (0:ℝ) T))
    (hder : ∀ r∈Ioo (0:ℝ) T,HasDerivAt z (dz r) r)
    (hbound : ∀ r∈Icc (0:ℝ) T,‖dz r‖≤K*‖z r‖) :
    ∀ t∈Icc (0:ℝ) T,‖z t‖≤‖z T‖*Real.exp (K*T) := by
  have hm : MapsTo (fun r:ℝ => T-r) (Icc (0:ℝ) T) (Icc (0:ℝ) T) :=
    fun r hr => ⟨sub_nonneg.mpr hr.2,sub_le_self _ hr.1⟩
  have hc : Continuous (fun r:ℝ => T-r) := continuous_const.sub continuous_id
  have he (r : ℝ) (hr : r∈Ioo (0:ℝ) T) :
      HasDerivAt (fun u => z (T-u)) (-dz (T-r)) r := by
    have hd := (hder (T-r) ⟨by linarith [hr.2],by linarith [hr.1]⟩).scomp r
      ((hasDerivAt_id r).const_sub T)
    simpa only [one_smul,neg_smul,Function.comp_def] using hd
  have hh := norm_ode_volterra_bound hT (hz.comp hc.continuousOn hm)
    (hdz.neg.comp hc.continuousOn hm) continuousOn_const (fun _ _ => hK) he (fun r hr => by
      simpa only [Function.comp_apply,Pi.neg_apply,norm_neg] using hbound (T-r) (hm hr))
  intro t ht
  have h := hh (T-t) (hm ht)
  simp only [Function.comp_apply,sub_zero,sub_sub_cancel,intervalIntegral.integral_const,smul_eq_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [ht.1])) (norm_nonneg _))

lemma backward_norm_ode_inhomogeneous_bound {z dz : ℝ → E} {c : ℝ → ℝ} {T K : ℝ}
    (hT : 0≤T) (hK : 0≤K)
    (hz : ContinuousOn z (Icc (0:ℝ) T)) (hdz : ContinuousOn dz (Icc (0:ℝ) T))
    (hc : ContinuousOn c (Icc (0:ℝ) T)) (hc0 : ∀ r∈Icc (0:ℝ) T,0≤c r)
    (hder : ∀ r∈Ioo (0:ℝ) T,HasDerivAt z (dz r) r)
    (hbound : ∀ r∈Icc (0:ℝ) T,‖dz r‖≤K*‖z r‖+c r) :
    ‖z 0‖≤(‖z T‖+∫ r in 0..T,c r)*Real.exp (K*T) := by
  have hm : MapsTo (fun r:ℝ => T-r) (Icc (0:ℝ) T) (Icc (0:ℝ) T) :=
    fun r hr => ⟨sub_nonneg.mpr hr.2,sub_le_self _ hr.1⟩
  have hc' : Continuous (fun r:ℝ => T-r) := continuous_const.sub continuous_id
  have he (r : ℝ) (hr : r∈Ioo (0:ℝ) T) :
      HasDerivAt (fun u => z (T-u)) (-dz (T-r)) r := by
    have hd := (hder (T-r) ⟨by linarith [hr.2],by linarith [hr.1]⟩).scomp r
      ((hasDerivAt_id r).const_sub T)
    simpa only [one_smul,neg_smul,Function.comp_def] using hd
  have hh := norm_ode_inhomogeneous_bound hT hK (hz.comp hc'.continuousOn hm)
    (hdz.neg.comp hc'.continuousOn hm) (hc.comp hc'.continuousOn hm)
    (fun r hr => hc0 (T-r) (hm hr)) he (fun r hr => by
      simpa only [Function.comp_apply,Pi.neg_apply,norm_neg] using hbound (T-r) (hm hr)) T ⟨hT,le_rfl⟩
  simpa only [Function.comp_apply,sub_self,sub_zero,intervalIntegral.integral_comp_sub_left] using hh

end

lemma exists_phase_characteristic_before {d : Datum} {s : Solution} {T U : ℝ}
    (hs : ClassicalBefore d s U) (hT : 0≤T) (hTU : T≤U) (z : Phase) :
    ∃ α : ℝ → Phase, α T=z ∧ ContinuousOn α (Icc (0:ℝ) T) ∧
      (∀ r∈Ioo (0:ℝ) T,HasDerivAt α (lorentzField s.E s.B (r,α r)) r) ∧
      s.f (T,z)=d.f₀ (α 0) := by
  obtain ⟨X,V,hXT,hVT,hX,hV,_⟩ := exists_characteristic_on_slab hT ⟨hT,le_rfl⟩ hs.2.1 hs.2.2.1 z.1 z.2
  have hXc : ContinuousOn X (Icc 0 T) := fun r hr => (hX r hr).continuousWithinAt
  have hVc : ContinuousOn V (Icc 0 T) := fun r hr => (hV r hr).continuousWithinAt
  have hdX := fun r hr => (hX r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have hdV := fun r hr => (hV r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have hf := transport_on_characteristic_before hs.1 hs.2.2.2.2.2.2.2.1 hT hTU hXc hVc hdX hdV
  rw [hXT,hVT,hs.2.2.2.2.2.2.2.2.1] at hf
  exact ⟨fun r => (X r,V r),by simp [hXT,hVT],hXc.prodMk hVc,
    fun r hr => (hdX r hr).prodMk (hdV r hr),hf⟩

lemma characteristic_separation_uniform {E B : Field} {α γ : ℝ → Phase} {T L N : ℝ}
    (hT : 0≤T) (hL : 0≤L) (hN : 0≤N)
    (hE : ContDiffOn ℝ 1 E fieldHalfSpace) (hB : ContDiffOn ℝ 1 B fieldHalfSpace)
    (hα : ContinuousOn α (Icc (0:ℝ) T)) (hγ : ContinuousOn γ (Icc (0:ℝ) T))
    (hdα : ∀ r∈Ioo (0:ℝ) T,HasDerivAt α (lorentzField E B (r,α r)) r)
    (hdγ : ∀ r∈Ioo (0:ℝ) T,HasDerivAt γ (lorentzField E B (r,γ r)) r)
    (hBb : ∀ r∈Icc (0:ℝ) T,∀ x,‖B (r,x)‖≤L)
    (hEx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖E (r,y)-E (r,x)‖≤N*‖y-x‖)
    (hBx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖B (r,y)-B (r,x)‖≤N*‖y-x‖) :
    ∀ r∈Icc (0:ℝ) T,‖α r-γ r‖≤‖α T-γ T‖*Real.exp ((1+2*N+L)*T) := by
  apply backward_norm_ode_uniform_bound hT (by positivity : 0≤1+2*N+L) (hα.sub hγ)
    ((continuousOn_lorentz_along hE hB hα).sub (continuousOn_lorentz_along hE hB hγ))
    (fun r hr => (hdα r hr).sub (hdγ r hr))
  intro r hr
  exact (lorentzField_difference_bound hL hN (D:=0) le_rfl (hBb r hr) (hEx r hr) (hBx r hr)
    (by intros; simp) (by intros; simp) (α r) (γ r)).trans_eq (by simp)

lemma characteristic_curvature_volterra {E B : Field} {α β γ : ℝ → Phase}
    {T L N : ℝ} {g : ℝ → ℝ} {z v : Phase}
    (hT : 0≤T) (hL : 0≤L) (hN : 0≤N)
    (hE : ContDiffOn ℝ 1 E fieldHalfSpace) (hB : ContDiffOn ℝ 1 B fieldHalfSpace)
    (hα : ContinuousOn α (Icc (0:ℝ) T)) (hβ : ContinuousOn β (Icc (0:ℝ) T))
    (hγ : ContinuousOn γ (Icc (0:ℝ) T))
    (hdα : ∀ r∈Ioo (0:ℝ) T,HasDerivAt α (lorentzField E B (r,α r)) r)
    (hdβ : ∀ r∈Ioo (0:ℝ) T,HasDerivAt β (lorentzField E B (r,β r)) r)
    (hdγ : ∀ r∈Ioo (0:ℝ) T,HasDerivAt γ (lorentzField E B (r,γ r)) r)
    (hαT : α T=z+v) (hβT : β T=z-v) (hγT : γ T=z)
    (hBb : ∀ r∈Icc (0:ℝ) T,∀ x,‖B (r,x)‖≤L)
    (hEx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖E (r,y)-E (r,x)‖≤N*‖y-x‖)
    (hBx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖B (r,y)-B (r,x)‖≤N*‖y-x‖)
    (hg : ContinuousOn g (Icc (0:ℝ) T)) (hg0 : ∀ r∈Icc (0:ℝ) T,0≤g r)
    (hEc : ∀ r∈Icc (0:ℝ) T,CurvatureBound (fun x => E (r,x)) (g r))
    (hBc : ∀ r∈Icc (0:ℝ) T,CurvatureBound (fun x => B (r,x)) (g r)) :
    ‖α 0+β 0-(2:ℝ) • γ 0‖≤
      (4*(Real.exp ((1+2*N+L)*T))^3*(∫ r in 0..T,6+6*L+2*g r+2*N))*‖v‖^2 := by
  let K := 1+2*N+L
  let Q := Real.exp (K*T)
  let C := fun r => 6+6*L+2*g r+2*N
  let δ := fun r => α r+β r-(2:ℝ) • γ r
  let dδ := fun r => lorentzField E B (r,α r)+lorentzField E B (r,β r)-
    (2:ℝ) • lorentzField E B (r,γ r)
  have hK : 0≤K := by dsimp [K]; positivity
  have hQ : 0<Q := Real.exp_pos _
  have hC : ∀ r∈Icc (0:ℝ) T,0≤C r := by intro r hr; dsimp [C]; have := hg0 r hr; positivity
  have hdc : ContinuousOn δ (Icc (0:ℝ) T) := (hα.add hβ).sub (hγ.const_smul (2:ℝ))
  have hddc : ContinuousOn dδ (Icc (0:ℝ) T) :=
    ((continuousOn_lorentz_along hE hB hα).add (continuousOn_lorentz_along hE hB hβ)).sub
      ((continuousOn_lorentz_along hE hB hγ).const_smul (2:ℝ))
  have hder : ∀ r∈Ioo (0:ℝ) T,HasDerivAt δ (dδ r) r :=
    fun r hr => ((hdα r hr).add (hdβ r hr)).sub ((hdγ r hr).const_smul (2:ℝ))
  have hsep := characteristic_separation_uniform hT hL hN hE hB hα hβ hdα hdβ hBb hEx hBx
  have hdT : δ T=0 := by dsimp [δ]; rw [hαT,hβT,hγT]; module
  have hb : ∀ r∈Icc (0:ℝ) T,‖dδ r‖≤K*‖δ r‖+(4*Q^2*‖v‖^2)*C r := by
    intro r hr
    have hf := lorentzField_curvature hL hN (hg0 r hr) (hBb r hr) (hBx r hr) (hEc r hr) (hBc r hr)
    have hfl (a b : Phase) : ‖lorentzField E B (r,b)-lorentzField E B (r,a)‖≤K*‖b-a‖ := by
      simpa only [mul_zero,add_zero] using lorentzField_difference_bound hL hN (D:=0) le_rfl
        (hBb r hr) (hEx r hr) (hBx r hr) (by intros; simp) (by intros; simp) b a
    have htr := hf.triple (hC r hr) hK hfl (α r) (β r) (γ r)
    have hs := hsep r hr
    rw [hαT,hβT,show z+v-(z-v)=(2:ℝ) • v by module,norm_smul,Real.norm_eq_abs] at hs
    norm_num at hs
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*‖v‖*Q)).mpr hs
    have hh := mul_le_mul_of_nonneg_left hsq (hC r hr)
    change ‖_‖≤K*‖α r+β r-(2:ℝ) • γ r‖+_
    nlinarith [htr,hh]
  have hc : ContinuousOn (fun r => (4*Q^2*‖v‖^2)*C r) (Icc (0:ℝ) T) := by dsimp [C]; fun_prop
  have hh := backward_norm_ode_inhomogeneous_bound hT hK hdc hddc hc
    (fun r hr => mul_nonneg (by positivity) (hC r hr)) hder hb
  rw [hdT,norm_zero,zero_add,intervalIntegral.integral_const_mul] at hh
  exact hh.trans_eq (by dsimp [δ,Q,K,C]; ring)

lemma particle_curvature_volterra_before {d : Datum} {s : Solution} {T U A D L N : ℝ}
    {g : ℝ → ℝ} (hs : ClassicalBefore d s U) (hT : 0≤T) (hTU : T≤U)
    (hA : 0≤A) (hD : 0≤D) (hL : 0≤L) (hN : 0≤N)
    (h₀ : ∀ z w,|d.f₀ z-d.f₀ w|≤A*‖z-w‖) (hc₀ : CurvatureBound d.f₀ D)
    (hg : ContinuousOn g (Icc (0:ℝ) T)) (hg0 : ∀ r∈Icc (0:ℝ) T,0≤g r)
    (hBb : ∀ r∈Icc (0:ℝ) T,∀ x,‖s.B (r,x)‖≤L)
    (hEx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖s.E (r,y)-s.E (r,x)‖≤N*‖y-x‖)
    (hBx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖s.B (r,y)-s.B (r,x)‖≤N*‖y-x‖)
    (hEc : ∀ r∈Icc (0:ℝ) T,CurvatureBound (fun x => s.E (r,x)) (g r))
    (hBc : ∀ r∈Icc (0:ℝ) T,CurvatureBound (fun x => s.B (r,x)) (g r)) :
    CurvatureBound (fun z => s.f (T,z))
      (4*D*(Real.exp ((1+2*N+L)*T))^2+
        A*4*(Real.exp ((1+2*N+L)*T))^3*(∫ r in 0..T,6+6*L+2*g r+2*N)) := by
  intro z v
  obtain ⟨α,hαT,hα,hdα,hfα⟩ := exists_phase_characteristic_before hs hT hTU (z+v)
  obtain ⟨β,hβT,hβ,hdβ,hfβ⟩ := exists_phase_characteristic_before hs hT hTU (z-v)
  obtain ⟨γ,hγT,hγ,hdγ,hfγ⟩ := exists_phase_characteristic_before hs hT hTU z
  have hfL (a b : Phase) : ‖d.f₀ b-d.f₀ a‖≤A*‖b-a‖ := h₀ b a
  have ht := hc₀.triple hD hA hfL (α 0) (β 0) (γ 0)
  have hc := characteristic_curvature_volterra hT hL hN hs.2.1 hs.2.2.1 hα hβ hγ
    hdα hdβ hdγ hαT hβT hγT hBb hEx hBx hg hg0 hEc hBc
  have hsep := characteristic_separation_uniform hT hL hN hs.2.1 hs.2.2.1 hα hβ
    hdα hdβ hBb hEx hBx 0 ⟨le_rfl,hT⟩
  rw [hαT,hβT,show z+v-(z-v)=(2:ℝ) • v by module,norm_smul,Real.norm_eq_abs] at hsep
  norm_num at hsep
  have hp := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hsep
  have hd := mul_le_mul_of_nonneg_left hp hD
  have ha := mul_le_mul_of_nonneg_left hc hA
  simp only [hfα,hfβ,hfγ]
  nlinarith [ht,hd,ha]


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

lemma CurvatureBound.fderiv_lipschitz {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H : ℝ} (hc : CurvatureBound f H) (hH : 0≤H)
    (hf : Differentiable ℝ f) :
    ∀ x y, ‖fderiv ℝ f y-fderiv ℝ f x‖≤6*H*‖y-x‖ := by
  have htaylor (basePoint increment : U) :
      ‖f (basePoint+increment)-f basePoint-fderiv ℝ f basePoint increment‖≤H*‖increment‖^2 := by
    let dyadicSequence : ℕ → W := fun index =>
      (2:ℝ)^index • (f (basePoint+(1/2:ℝ)^index • increment)-f basePoint)
    have hderivative : HasDerivAt (fun time : ℝ => f (basePoint+time • increment))
        (fderiv ℝ f basePoint increment) 0 := by
      have hcomposition := (hf (basePoint+(0:ℝ) • increment)).hasFDerivAt.comp_hasDerivAt (0:ℝ)
        ((hasDerivAt_const (0:ℝ) basePoint).add ((hasDerivAt_id (0:ℝ)).smul_const increment))
      simpa only [zero_smul,add_zero,one_smul,zero_add,Function.comp_def,Pi.add_apply,id_eq] using hcomposition
    have hpowers : Tendsto (fun index : ℕ => (1/2:ℝ)^index) atTop (𝓝[>] (0:ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
        Eventually.of_forall (fun index => by simp only [mem_Ioi]; positivity)⟩
    have hlimit : Tendsto dyadicSequence atTop (𝓝 (fderiv ℝ f basePoint increment)) := by
      simpa [Function.comp_def,dyadicSequence,← inv_pow] using hderivative.tendsto_slope_zero_right.comp hpowers
    have hstep (index : ℕ) : dist (dyadicSequence index) (dyadicSequence (index+1))≤
        (H*‖increment‖^2/2)*(1/2:ℝ)^index := by
      let scale : ℝ := (1/2:ℝ)^index
      have hscale : 0 ≤ scale := by dsimp [scale]; positivity
      have hpower : 0≤(2:ℝ)^index := by positivity
      have hinverse : (2:ℝ)^index*scale=1 := by dsimp [scale]; rw [← mul_pow]; norm_num
      have hcenter := hc (basePoint+(scale/2) • increment) ((scale/2) • increment)
      rw [show (basePoint+(scale/2) • increment)+(scale/2) • increment=basePoint+scale • increment by module,
        show (basePoint+(scale/2) • increment)-(scale/2) • increment=basePoint by module,
        norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ scale/2)] at hcenter
      have hdifference : dyadicSequence index-dyadicSequence (index+1)=
          (2:ℝ)^index • (f (basePoint+scale • increment)+f basePoint-
            (2:ℝ) • f (basePoint+(scale/2) • increment)) := by
        dsimp only [dyadicSequence]
        rw [pow_succ,pow_succ]
        change (2:ℝ)^index • (f (basePoint+scale • increment)-f basePoint)-
          ((2:ℝ)^index*2) • (f (basePoint+(scale*(1/2)) • increment)-f basePoint)=_
        rw [show scale*(1/2)=scale/2 by ring]
        module
      rw [dist_eq_norm,hdifference,norm_smul,Real.norm_eq_abs,abs_of_nonneg hpower]
      apply (mul_le_mul_of_nonneg_left hcenter hpower).trans
      have hequality : (2:ℝ)^index*(H*(scale/2*‖increment‖)^2)=(H*‖increment‖^2/4)*scale := by
        calc
          _ = (H*‖increment‖^2/4)*((2:ℝ)^index*scale)*scale := by ring
          _ = _ := by rw [hinverse]; ring
      rw [hequality]
      change (H*‖increment‖^2/4)*scale≤(H*‖increment‖^2/2)*scale
      gcongr
      nlinarith [mul_nonneg hH (sq_nonneg ‖increment‖)]
    have hgeometric := dist_le_of_le_geometric_of_tendsto₀
      (r:=(1/2:ℝ)) (C:=H*‖increment‖^2/2) (by norm_num) hstep hlimit
    simpa only [dyadicSequence,pow_zero,one_smul,dist_eq_norm,
      show (H*‖increment‖^2/2)/(1-(1/2:ℝ))=H*‖increment‖^2 by ring] using hgeometric
  intro x y
  by_cases he : y=x
  · subst y; simp
  have hr : 0<‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  let r := ‖y-x‖
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let w := r • v
  have hw : ‖w‖=r := by dsimp [w]; rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hv,mul_one]
  have h1 := htaylor x (y+w-x)
  have h2 := htaylor x (y-x)
  have h3 := htaylor y w
  rw [show x+(y+w-x)=y+w by abel] at h1
  rw [show x+(y-x)=y by abel] at h2
  let R1 := f (y+w)-f x-fderiv ℝ f x (y+w-x)
  let R2 := f y-f x-fderiv ℝ f x (y-x)
  let R3 := f (y+w)-f y-fderiv ℝ f y w
  have hid : (fderiv ℝ f y-fderiv ℝ f x) w=R1-R2-R3 := by
    dsimp [R1,R2,R3]
    simp only [sub_apply,map_sub,map_add]
    abel
  have hnorm : ‖y+w-x‖≤2*r := by
    rw [show y+w-x=(y-x)+w by abel]
    exact (norm_add_le _ _).trans (by rw [hw]; change r+r≤2*r; linarith)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*r)).mpr hnorm
  have hb : ‖(fderiv ℝ f y-fderiv ℝ f x) w‖≤6*H*r^2 := by
    rw [hid]
    have h := (norm_sub_le (R1-R2) R3).trans (add_le_add (norm_sub_le R1 R2) (le_refl ‖R3‖))
    rw [hw] at h3
    have hp := mul_le_mul_of_nonneg_left hsq hH
    nlinarith [h,h1,h2,h3,hp]
  rw [show (fderiv ℝ f y-fderiv ℝ f x) w=r • ((fderiv ℝ f y-fderiv ℝ f x) v) by
    exact map_smul _ _ _,norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hb
  change ‖(fderiv ℝ f y-fderiv ℝ f x) v‖≤6*H*r
  nlinarith

lemma CurvatureBound.second_derivative_bound {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H : ℝ} (hc : CurvatureBound f H) (hH : 0≤H)
    (hf : Differentiable ℝ f) (x : U) : ‖iteratedFDeriv ℝ 2 f x‖≤6*H := by
  have hL : LipschitzWith ⟨6*H,by positivity⟩ (fderiv ℝ f) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    change dist (fderiv ℝ f y) (fderiv ℝ f z)≤(6*H)*dist y z
    simpa only [dist_eq_norm] using hc.fderiv_lipschitz hH hf z y
  have hh := norm_fderiv_le_of_lipschitz ℝ hL (x₀:=x)
  change ‖fderiv ℝ (fderiv ℝ f) x‖≤6*H at hh
  simpa only [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv] using hh

end RVM

end

end OAI
