import Mathlib
import OAI.Analysis.VlasovMaxwell.Maxwell.WaveGradient
import OAI.Analysis.VlasovMaxwell.Retarded.PhysicalElectricKernel

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set


lemma selection_unsafe_actual
    {α z c b y H Δ : ℝ}
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hy : 0 ≤ y) (hH : 0 ≤ H) (hzc : z+c=1)
    (hΔ : Δ=(α+b+y+H)/100000)
    (hnear : 2*α+H/2+2*y < z+Δ)
    (hfar : if H ≤ 2*c then b<H/2-α+Δ else b<H-c-α+Δ)
    (hu₁ : 2*H/3+z/6-Δ/3 < b)
    (hu₂ : b<H+2*y-z/2+Δ) :
    0 < z ∧ 0 ≤ Δ ∧ Δ<z/1000 ∧ 2*c<H ∧
      z/2+3*(α+c)-4*Δ<H ∧
      7/2*α+3/2*c+2*y<753/1000*z ∧
      500/751<z ∧ 623/1000<z-y ∧ 623/1000<1-α-y := by
  have hΔ0 : 0 ≤ Δ := by rw [hΔ]; positivity
  have hf : b<H-α+Δ := by
    split_ifs at hfar with ha <;> linarith
  have hd : Δ<4/99995*z := by linarith
  have hz0 : 0<z := by linarith
  have hdsmall : Δ<z/1000 := by linarith
  have hh : 2*c<H := by
    by_contra hn
    have hh' : H≤2*c := le_of_not_gt hn
    rw [ite_eq_left hh'] at hfar
    linarith
  rw [ite_eq_right (not_le.mpr hh)] at hfar
  have hlow : z/2+3*(α+c)-4*Δ<H := by linarith
  have hmargin : 7/2*α+3/2*c+2*y<753/1000*z := by linarith
  refine ⟨hz0,hΔ0,hdsmall,hh,hlow,hmargin,?_,?_,?_⟩ <;> linarith

lemma selection_unsafe_window
    {α z c b y H Δ : ℝ}
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hy : 0 ≤ y) (hH : 0 ≤ H) (hzc : z+c=1)
    (hΔ : Δ=(α+b+y+H)/100000)
    (hnear : 2*α+H/2+2*y < z+Δ)
    (hfar : if H ≤ 2*c then b<H/2-α+Δ else b<H-c-α+Δ)
    (hu₁ : 2*H/3+z/6-Δ/3 < b)
    (hu₂ : b<H+2*y-z/2+Δ)
    (hstable : b<H/2-min α c+y+z/500) :
    7/10<z ∧ 7/10<1-α ∧
      4/25*max z (1-α)<y ∧ y<49/100*min z (1-α) := by
  obtain ⟨hz0,hΔ0,hd,hh,hlow,hm,hzlow,hzy,hαy⟩ :=
    selection_unsafe_actual hα hz hc hb hy hH hzc hΔ hnear hfar hu₁ hu₂
  have hmin : 0 ≤ min α c := le_min hα hc
  have hmiddle : H/3+328/1000*z+2*min α c<2*y := by linarith
  have hupper : H<81/100*z := by linarith
  have hsum : α+c<105/1000*z := by linarith
  have hz9 : 9/10<z := by linarith
  have hα9 : 895/1000<1-α := by linarith
  have hy19 : 19/100*z<y := by linarith
  have hy17 : 171/1000<y := by linarith
  refine ⟨by linarith,by linarith,?_,?_⟩
  · rcases le_total z (1-α) with he | he
    · rw [max_eq_right he]; linarith
    · rw [max_eq_left he]; linarith
  · rcases le_total z (1-α) with he | he
    · rw [min_eq_left he]; linarith
    · rw [min_eq_right he]; linarith

lemma selection_unsafe_contradiction
    {α z c b y H Δ : ℝ}
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hy : 0 ≤ y) (hH : 0 ≤ H) (hzc : z+c=1)
    (hΔ : Δ=(α+b+y+H)/100000)
    (hnear : 2*α+H/2+2*y < z+Δ)
    (hfar : if H ≤ 2*c then b<H/2-α+Δ else b<H-c-α+Δ)
    (hu₁ : 2*H/3+z/6-Δ/3 < b)
    (hu₂ : b<H+2*y-z/2+Δ)
    (himproved : b<H/2-min α c+29/50*y+Δ) : False := by
  obtain ⟨hz0,hΔ0,hd,hh,hlow,hm,hzlow,hzy,hαy⟩ :=
    selection_unsafe_actual hα hz hc hb hy hH hzc hΔ hnear hfar hu₁ hu₂
  have hmin : 0 ≤ min α c := le_min hα hc
  linarith

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma integrableOn_norm_rpow_neg {α R : ℝ} (hα : α<3) :
    IntegrableOn (fun z : Vec => ‖z‖ ^ (-α)) (ball (0:Vec) R) := by
  apply integrableOn_ball_of_norm_le_rpow (by simp) (C:=1) (α:=α) (by simpa using hα)
  · exact ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]; simp)
  · exact (continuous_norm.measurable.pow measurable_const).aestronglyMeasurable

lemma integral_ball_norm_rpow_neg {α R : ℝ} (hα : α<3) (hR : 0≤R) :
    (∫ z in ball (0:Vec) R, ‖z‖ ^ (-α)) =
      (4*Real.pi) * R^(3-α)/(3-α) := by
  rw [← integral_indicator measurableSet_ball,
    integral_polar ((integrableOn_norm_rpow_neg hα).integrable_indicator measurableSet_ball)]
  have he (n : Sphere) :
      (∫ r in Ioi (0:ℝ), r^2 • (ball (0:Vec) R).indicator
        (fun z => ‖z‖^(-α)) (r • n.1)) = R^(3-α)/(3-α) := by
    have heq : ∀ r ∈ Ioi (0:ℝ), r^2 • (ball (0:Vec) R).indicator
        (fun z => ‖z‖^(-α)) (r • n.1) =
        (Ioo (0:ℝ) R).indicator (fun r => r^(2-α)) r := by
      intro r hr
      change 0<r at hr
      have hn : ‖r • n.1‖=r := by simp [norm_smul,abs_of_pos hr]
      by_cases h : r<R
      · rw [indicator_of_mem (show r • n.1 ∈ ball (0:Vec) R by simpa [mem_ball_zero_iff,hn] using h),
          indicator_of_mem (show r ∈ Ioo (0:ℝ) R from ⟨hr,h⟩),hn,smul_eq_mul]
        rw [← Real.rpow_two,← Real.rpow_add hr]
        congr 1
      · rw [indicator_of_notMem (show r • n.1 ∉ ball (0:Vec) R by simpa [mem_ball_zero_iff,hn] using h),
          indicator_of_notMem (show r ∉ Ioo (0:ℝ) R from fun hh => h hh.2),smul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi heq,setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self,← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hR,integral_rpow (Or.inl (by linarith : -1<2-α))]
    have hne : 2-α+1≠0 := by linarith
    rw [Real.zero_rpow hne,sub_zero]
    rw [show 2-α+1=3-α by ring]
  simp_rw [he]
  rw [integral_const,smul_eq_mul,sphere_area]
  ring

lemma norm_integral_tip_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {C α R : ℝ} (hα : α<3) (hR : 0≤R)
    (hF : AEStronglyMeasurable F)
    (hbound : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), ‖F z‖≤C*‖z‖^(-α)) :
    ‖∫ z in ball (0:Vec) R, F z‖ ≤ C*(4*Real.pi)*R^(3-α)/(3-α) := by
  have hi := integrableOn_norm_rpow_neg (R:=R) hα
  calc
    _ ≤ ∫ z in ball (0:Vec) R, ‖F z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in ball (0:Vec) R, C*‖z‖^(-α) := by
      apply integral_mono_ae
        ((integrableOn_ball_of_norm_le_rpow (by simp) (by simpa using hα) hbound hF).norm)
        (hi.const_mul C) hbound
    _ = _ := by rw [integral_const_mul,integral_ball_norm_rpow_neg hα hR]; ring

lemma potential_tip_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {C R : ℝ} (hR : 0≤R) (hF : AEStronglyMeasurable F)
    (hbound : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), ‖F z‖≤C/‖z‖) :
    ‖∫ z in ball (0:Vec) R, F z‖ ≤ 2*Real.pi*C*R^2 := by
  have hb : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), ‖F z‖≤C*‖z‖^(-(1:ℝ)) := by
    simpa only [Real.rpow_neg_one,div_eq_mul_inv] using hbound
  have hh := norm_integral_tip_le (by norm_num : (1:ℝ)<3) hR hF hb
  norm_num only [show (3:ℝ)-1=2 by norm_num,Real.rpow_two] at hh
  convert hh using 1; ring

lemma kernel_tip_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {C R : ℝ} (hR : 0≤R) (hF : AEStronglyMeasurable F)
    (hbound : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), ‖F z‖≤C/‖z‖^2) :
    ‖∫ z in ball (0:Vec) R, F z‖ ≤ 4*Real.pi*C*R := by
  have hb : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), ‖F z‖≤C*‖z‖^(-(2:ℝ)) := by
    simpa only [Real.rpow_neg (norm_nonneg _),Real.rpow_two,div_eq_mul_inv] using hbound
  have hh := norm_integral_tip_le (by norm_num : (2:ℝ)<3) hR hF hb
  norm_num only [show (3:ℝ)-2=1 by norm_num,Real.rpow_one,div_one] at hh
  convert hh using 1; ring

lemma dot_zero_right_rvm (a : Vec) : dot a 0=0 := by simp [dot]
lemma dot_zero_left_rvm (a : Vec) : dot 0 a=0 := by simp [dot]

lemma hasDerivAt_norm_nonzero {Y : ℝ → Vec} {u : Vec} {s : ℝ}
    (hY : HasDerivAt Y u s) (h0 : Y s≠0) :
    HasDerivAt (fun t => ‖Y t‖) (dot (Y s) u / ‖Y s‖) s := by
  have hn := (hY.differentiableAt.norm ℝ h0).hasDerivAt
  have he := (hn.pow 2).unique hY.norm_sq
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,← dot_eq_inner] at he
  have hr : ‖Y s‖≠0 := norm_ne_zero_iff.mpr h0
  have he' : deriv (fun t => ‖Y t‖) s = dot (Y s) u / ‖Y s‖ := by
    apply (eq_div_iff hr).mpr
    linarith
  rwa [he'] at hn

def coneRadius (x y : Vec) : ℝ := ‖x-y‖
def coneDirection (x y : Vec) : Vec := (coneRadius x y)⁻¹ • (x-y)

lemma coneDirection_norm {x y : Vec} (h : x≠y) : ‖coneDirection x y‖=1 := by
  have hr : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  simp [coneDirection,coneRadius,norm_smul,hr.ne']

lemma hasDerivAt_coneRadius {Y : ℝ → Vec} {u x : Vec} {s : ℝ}
    (hY : HasDerivAt Y u s) (h : x≠Y s) :
    HasDerivAt (coneRadius x ∘ Y) (-dot (coneDirection x (Y s)) u) s := by
  have hh := hasDerivAt_norm_nonzero ((hasDerivAt_const s x).sub hY)
    (sub_ne_zero.mpr h)
  convert hh using 1
  · rfl
  · simp only [coneDirection,coneRadius,dot_smul_left,zero_sub,Pi.sub_apply]
    simp only [dot,PiLp.neg_apply,mul_neg,Finset.sum_neg_distrib]
    ring

lemma hasDerivAt_eulerian_direction {Y : ℝ → Vec} {u x : Vec} {s : ℝ}
    (hY : HasDerivAt Y u s) (h : x≠Y s) :
    HasDerivAt (coneDirection x ∘ Y)
      ((coneRadius x (Y s))⁻¹ •
        (dot (coneDirection x (Y s)) u • coneDirection x (Y s)-u)) s := by
  have hr := hasDerivAt_coneRadius hY h
  have hr0 : coneRadius x (Y s)≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  have hh := (hr.inv hr0).smul ((hasDerivAt_const s x).sub hY)
  convert hh using 1 <;> try rfl
  ext i
  simp only [coneDirection,coneRadius,Function.comp_apply,Pi.inv_apply,Pi.sub_apply,PiLp.neg_apply,PiLp.add_apply,
      PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,zero_sub,dot_smul_left]
  ring

def eulerianG (r : ℝ) (n u : Vec) : Vec := (r*(1-dot n u))⁻¹ • (n-u)

lemma hasDerivAt_eulerianG_space {r : ℝ → ℝ} {n : ℝ → Vec} {u : Vec} {s : ℝ}
    (hr : HasDerivAt r (-dot (n s) u) s)
    (hn : HasDerivAt n ((r s)⁻¹ • (dot (n s) u • n s-u)) s)
    (hr0 : r s≠0) (hd : 1-dot (n s) u≠0) :
    HasDerivAt (fun t => eulerianG (r t) (n t) u)
      (((1-dot u u)/((r s)^2*(1-dot (n s) u)^2)) • (n s-u) -
        ((r s)^2)⁻¹ • n s) s := by
  have hd' := (hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_dot hn (hasDerivAt_const s u))
  have hh := ((hr.mul hd').inv (mul_ne_zero hr0 hd)).smul
    (hn.sub (hasDerivAt_const s u))
  convert hh using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply,Pi.mul_apply,Pi.sub_apply,PiLp.add_apply,PiLp.sub_apply,
      PiLp.smul_apply,smul_eq_mul,dot_smul_left,dot_sub_left,
      dot_zero_right_rvm,zero_add,sub_zero,zero_sub]
  field_simp
  ring

lemma hasDerivAt_eulerianG_velocity {u : ℝ → Vec} {b n : Vec} {r s : ℝ}
    (hu : HasDerivAt u b s) (hr : r≠0) (hd : 1-dot n (u s)≠0) :
    HasDerivAt (fun t => eulerianG r n (u t))
      ((r*(1-dot n (u s))^2)⁻¹ •
        ((dot n b) • (n-u s)-(1-dot n (u s)) • b)) s := by
  have hd' := (hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_dot (hasDerivAt_const s n) hu)
  have hh := (((hasDerivAt_const s r).mul hd').inv (mul_ne_zero hr hd)).smul
    ((hasDerivAt_const s n).sub hu)
  convert hh using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply,Pi.mul_apply,Pi.sub_apply,PiLp.neg_apply,PiLp.add_apply,PiLp.sub_apply,
      PiLp.smul_apply,smul_eq_mul,dot_zero_left_rvm,zero_add,zero_mul,zero_sub]
  field_simp
  ring

lemma eulerian_kernel_decomposition (r : ℝ) (n u b : Vec)
    (hr : r≠0) (hd : 1-dot n u≠0) :
    (r^2)⁻¹ • n +
      (((1-dot u u)/(r^2*(1-dot n u)^2)) • (n-u)-(r^2)⁻¹ • n) +
      (r*(1-dot n u)^2)⁻¹ • ((dot n b) • (n-u)-(1-dot n u) • b) =
      (1-dot n u) • physicalElectricKernel r n u b := by
  ext i
  simp only [physicalElectricKernel,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  field_simp
  ring

lemma retarded_transport_chain {f : Particle} {x y v u K : Vec} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t-coneRadius x y,y,v)) (hxy : x≠y) :
    fderiv ℝ (fun z : Phase => f (t-coneRadius x z.1,z)) (y,v) (u,K) =
      fderiv ℝ f (t-coneRadius x y,y,v) (dot (coneDirection x y) u,u,K) := by
  let Y : ℝ → Vec := fun s => y+s • u
  let V : ℝ → Vec := fun s => v+s • K
  have hY : HasDerivAt Y u 0 := by
    have hh := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const u)
    change HasDerivAt Y (0+(1:ℝ) • u) 0 at hh
    simpa only [zero_add,one_smul] using hh
  have hV : HasDerivAt V K 0 := by
    have hh := (hasDerivAt_const (0:ℝ) v).add ((hasDerivAt_id (0:ℝ)).smul_const K)
    change HasDerivAt V (0+(1:ℝ) • K) 0 at hh
    simpa only [zero_add,one_smul] using hh
  have hr := hasDerivAt_coneRadius hY (by simpa [Y] using hxy)
  have hc := ((hasDerivAt_const (0:ℝ) t).sub hr).prodMk (hY.prodMk hV)
  have hf' : HasFDerivAt f (fderiv ℝ f (t-coneRadius x y,y,v))
      (t-coneRadius x (Y 0),Y 0,V 0) := by simpa only [Y,V,zero_smul,add_zero] using hf.hasFDerivAt
  have hh := hf'.comp_hasDerivAt (0:ℝ) hc
  have hinner : DifferentiableAt ℝ (fun z : Phase => (t-coneRadius x z.1,z)) (y,v) := by
    refine ((differentiableAt_const t).sub ?_).prodMk differentiableAt_id
    exact ((differentiableAt_const x).sub differentiableAt_fst).norm ℝ (sub_ne_zero.mpr hxy)
  have houter := hf.comp (f := fun z : Phase => (t-coneRadius x z.1,z)) (y,v) hinner
  have ho' : HasFDerivAt (fun z : Phase => f (t-coneRadius x z.1,z))
      (fderiv ℝ (fun z : Phase => f (t-coneRadius x z.1,z)) (y,v)) (Y 0,V 0) := by
    convert houter.hasFDerivAt using 1 <;> try rfl
    simp only [Y,V,zero_smul,add_zero]
  have hh' := ho'.comp_hasDerivAt (0:ℝ) (hY.prodMk hV)
  have he := hh'.unique hh
  simpa only [Y,V,zero_smul,add_zero,zero_sub,neg_neg] using he

lemma retarded_transport_identity {f : Particle} {x y v u K : Vec} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t-coneRadius x y,y,v)) (hxy : x≠y)
    (heq : fderiv ℝ f (t-coneRadius x y,y,v) (1,u,K)=0) :
    fderiv ℝ (fun z : Phase => f (t-coneRadius x z.1,z)) (y,v) (u,K) =
      -(1-dot (coneDirection x y) u)*fderiv ℝ f (t-coneRadius x y,y,v) (1,0,0) := by
  rw [retarded_transport_chain hf hxy]
  have hv : (dot (coneDirection x y) u,u,K) =
      (1,u,K)-(1-dot (coneDirection x y) u) • ((1:ℝ),(0:Vec),(0:Vec)) := by
    ext <;> simp
  rw [hv,map_sub,map_smul,heq]
  simp only [smul_eq_mul,zero_sub,neg_mul]

lemma classical_retarded_transport {s : Solution} {t : ℝ} {x y v : Vec}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (heq : Equations s)
    (ht : 0<t-coneRadius x y) (hxy : x≠y) :
    fderiv ℝ (fun z : Phase => s.f (t-coneRadius x z.1,z)) (y,v)
      (velocity v,s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y))) =
      -(1-dot (coneDirection x y) (velocity v))*
        fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0) := by
  have hd := particle_differentiableAt_positive hf ht y v
  apply retarded_transport_identity hd hxy
  simpa only [fderiv_particleBySpacetime hd] using particle_spacetime_vlasov hf heq ht y v

lemma dot_gradient_direction (g : Vec → ℝ) (y w : Vec) :
    dot (gradient g y) w=fderiv ℝ g y w := by
  rw [dot_comm,clm_sum_basis]
  simp only [dot,gradient_apply,spatialPartial]

lemma divergence_const_rvm (w y : Vec) : divergence (fun _ : Vec => w) y=0 := by
  simp [divergence,spatialPartial]

lemma fderiv_phase_split {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : Phase → H} {y v u K : Vec} (hg : DifferentiableAt ℝ g (y,v)) :
    fderiv ℝ (fun z => g (z,v)) y u+fderiv ℝ (fun w => g (y,w)) v K =
      fderiv ℝ g (y,v) (u,K) := by
  have hiy : HasFDerivAt (fun z : Vec => (z,v))
      ((ContinuousLinearMap.id ℝ Vec).prod (0 : Vec →L[ℝ] Vec)) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const v y)
  have hiv : HasFDerivAt (fun w : Vec => (y,w))
      ((0 : Vec →L[ℝ] Vec).prod (ContinuousLinearMap.id ℝ Vec)) v :=
    (hasFDerivAt_const y v).prodMk (hasFDerivAt_id v)
  have hy := hg.hasFDerivAt.comp y hiy
  have hv := hg.hasFDerivAt.comp v hiv
  have hy' : fderiv ℝ (fun z => g (z,v)) y u=fderiv ℝ g (y,v) (u,0) := by
    convert congrArg (fun L : Vec →L[ℝ] H => L u) hy.fderiv using 1 <;> rfl
  have hv' : fderiv ℝ (fun w => g (y,w)) v K=fderiv ℝ g (y,v) (0,K) := by
    convert congrArg (fun L : Vec →L[ℝ] H => L K) hv.fderiv using 1 <;> rfl
  rw [hy',hv']
  rw [← map_add]
  congr 1
  ext <;> simp

lemma phase_divergence_transport {g : Phase → ℝ} {K : Vec → Vec} {y v u : Vec}
    (hg : DifferentiableAt ℝ g (y,v)) (hK : DifferentiableAt ℝ K v) :
    divergence (fun z => g (z,v) • u) y+divergence (fun w => g (y,w) • K w) v =
      fderiv ℝ g (y,v) (u,K v)+g (y,v)*divergence K v := by
  have hy : DifferentiableAt ℝ (fun z => g (z,v)) y :=
    hg.comp (f := fun z => (z,v)) y (differentiableAt_id.prodMk (differentiableAt_const v))
  have hv : DifferentiableAt ℝ (fun w => g (y,w)) v :=
    hg.comp (f := fun w => (y,w)) v ((differentiableAt_const y).prodMk differentiableAt_id)
  rw [divergence_smul hy (differentiableAt_const u),divergence_smul hv hK,
    divergence_const_rvm,mul_zero,add_zero,dot_gradient_direction,dot_gradient_direction,
    ← add_assoc,fderiv_phase_split hg]

lemma hasDerivAt_line_rvm (y u : Vec) :
    HasDerivAt (fun s : ℝ => y+s • u) u 0 := by
  have hh := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const u)
  change HasDerivAt (fun s : ℝ => y+s • u) (0+(1:ℝ) • u) 0 at hh
  simpa only [zero_add,one_smul] using hh

lemma fderiv_of_line_rvm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : Vec → H} {y u : Vec} {w : H} (hg : DifferentiableAt ℝ g y)
    (hc : HasDerivAt (fun s : ℝ => g (y+s • u)) w 0) : fderiv ℝ g y u=w := by
  have h : HasFDerivAt g (fderiv ℝ g y) (y+(0:ℝ) • u) := by
    simpa only [zero_smul,add_zero] using hg.hasFDerivAt
  exact (h.comp_hasDerivAt 0 (hasDerivAt_line_rvm y u)).unique hc

lemma differentiableAt_coneRadius {x y : Vec} (h : x≠y) :
    DifferentiableAt ℝ (coneRadius x) y :=
  ((differentiableAt_const x).sub differentiableAt_id).norm ℝ (sub_ne_zero.mpr h)

lemma differentiableAt_coneDirection {x y : Vec} (h : x≠y) :
    DifferentiableAt ℝ (coneDirection x) y :=
  ((differentiableAt_coneRadius h).inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h))).smul
    ((differentiableAt_const x).sub differentiableAt_id)

lemma differentiableAt_eulerianG {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {r : H → ℝ} {n u : H → Vec} {s : H}
    (hr : DifferentiableAt ℝ r s) (hn : DifferentiableAt ℝ n s)
    (hu : DifferentiableAt ℝ u s) (hr0 : r s≠0) (hd : 1-dot (n s) (u s)≠0) :
    DifferentiableAt ℝ (fun z => eulerianG (r z) (n z) (u z)) s := by
  have hdot : DifferentiableAt ℝ (fun z => dot (n z) (u z)) s := by
    simpa only [dot_eq_inner] using hn.inner ℝ hu
  exact ((hr.mul ((differentiableAt_const (1:ℝ)).sub hdot)).inv
    (mul_ne_zero hr0 hd)).smul (hn.sub hu)

lemma fderiv_eulerianG_space {x y u : Vec} (hxy : x≠y)
    (hd : 1-dot (coneDirection x y) u≠0) :
    fderiv ℝ (fun z => eulerianG (coneRadius x z) (coneDirection x z) u) y u =
      ((1-dot u u)/((coneRadius x y)^2*(1-dot (coneDirection x y) u)^2)) •
        (coneDirection x y-u) - ((coneRadius x y)^2)⁻¹ • coneDirection x y := by
  have hr0 : coneRadius x y≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hg := differentiableAt_eulerianG (differentiableAt_coneRadius hxy)
    (differentiableAt_coneDirection hxy) (differentiableAt_const u) hr0 hd
  apply fderiv_of_line_rvm hg
  have hc := hasDerivAt_line_rvm y u
  have hxy' : x≠y+(0:ℝ) • u := by simpa only [zero_smul,add_zero] using hxy
  have hh := hasDerivAt_eulerianG_space
    (r := fun s => coneRadius x (y+s • u)) (n := fun s => coneDirection x (y+s • u))
    (u := u) (s := 0) (hasDerivAt_coneRadius hc hxy')
    (hasDerivAt_eulerian_direction hc hxy')
    (by simpa only [zero_smul,add_zero] using hr0)
    (by simpa only [zero_smul,add_zero] using hd)
  simpa only [Function.comp_apply,zero_smul,add_zero] using hh

lemma fderiv_eulerianG_velocity {r : ℝ} {n v K : Vec} (hr : r≠0)
    (hd : 1-dot n (velocity v)≠0) :
    fderiv ℝ (fun w => eulerianG r n (velocity w)) v K =
      (r*(1-dot n (velocity v))^2)⁻¹ •
        ((dot n (fderiv ℝ velocity v K)) • (n-velocity v)-
          (1-dot n (velocity v)) • (fderiv ℝ velocity v K)) := by
  have hv := (contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω)≠0)) v
  apply fderiv_of_line_rvm (differentiableAt_eulerianG
    (differentiableAt_const r) (differentiableAt_const n) hv hr hd)
  have hvel := hasDerivAt_particle_velocity (hasDerivAt_line_rvm v K)
  have hh := hasDerivAt_eulerianG_velocity hvel hr
    (by simpa only [zero_smul,add_zero] using hd)
  simpa only [zero_smul,add_zero,fderiv_velocity_apply] using hh

def retardedG (x : Vec) (z : Phase) : Vec :=
  eulerianG (coneRadius x z.1) (coneDirection x z.1) (velocity z.2)

lemma differentiableAt_retardedG {x y v : Vec} (hxy : x≠y) :
    DifferentiableAt ℝ (retardedG x) (y,v) := by
  apply differentiableAt_eulerianG (r := fun z : Phase => coneRadius x z.1)
    (n := fun z : Phase => coneDirection x z.1) (u := fun z : Phase => velocity z.2)
  · exact (differentiableAt_coneRadius hxy).comp (f:=Prod.fst) (y,v) differentiableAt_fst
  · exact (differentiableAt_coneDirection hxy).comp (f:=Prod.fst) (y,v) differentiableAt_fst
  · exact ((contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω)≠0)) v).comp
      (f:=Prod.snd) (y,v) differentiableAt_snd
  · exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  · exact (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne'

lemma fderiv_retardedG {x y v K : Vec} (hxy : x≠y) :
    fderiv ℝ (retardedG x) (y,v) (velocity v,K) =
      (1-dot (coneDirection x y) (velocity v)) •
        physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
          (fderiv ℝ velocity v K) - ((coneRadius x y)^2)⁻¹ • coneDirection x y := by
  have hd := (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne'
  have hr : coneRadius x y≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  rw [← fderiv_phase_split (differentiableAt_retardedG hxy)]
  change fderiv ℝ (fun z => eulerianG (coneRadius x z) (coneDirection x z) (velocity v)) y
    (velocity v)+fderiv ℝ (fun w => eulerianG (coneRadius x y) (coneDirection x y) (velocity w)) v K = _
  rw [fderiv_eulerianG_space hxy hd,fderiv_eulerianG_velocity hr hd]
  have he := eulerian_kernel_decomposition (coneRadius x y) (coneDirection x y)
    (velocity v) (fderiv ℝ velocity v K) hr hd
  exact eq_sub_of_add_eq (by simpa only [add_assoc,add_left_comm,add_comm] using he)

def retardedDensity (f : Particle) (t : ℝ) (x : Vec) (z : Phase) : ℝ :=
  f (t-coneRadius x z.1,z)

lemma differentiableAt_retardedDensity {f : Particle} {x y v : Vec} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t-coneRadius x y,y,v)) (hxy : x≠y) :
    DifferentiableAt ℝ (retardedDensity f t x) (y,v) := by
  have hi : DifferentiableAt ℝ (fun z : Phase => (t-coneRadius x z.1,z)) (y,v) :=
    ((differentiableAt_const t).sub ((differentiableAt_coneRadius hxy).comp
      (f:=Prod.fst) (y,v) differentiableAt_fst)).prodMk differentiableAt_id
  exact hf.comp (f := fun z : Phase => (t-coneRadius x z.1,z)) (y,v) hi

lemma fderiv_vec_component_at {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : H → Vec} {z e : H} (hg : DifferentiableAt ℝ g z) (i : Fin 3) :
    fderiv ℝ (fun w => g w i) z e=(fderiv ℝ g z e) i := by
  have h := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp z hg.hasFDerivAt
  convert congrArg (fun L : H →L[ℝ] ℝ => L e) h.fderiv using 1 <;> rfl

lemma retardedG_deficit_component {x y v : Vec} (hxy : x≠y) (i : Fin 3) :
    (1-dot (coneDirection x y) (velocity v))*retardedG x (y,v) i =
      (coneDirection x y i-velocity v i)/coneRadius x y := by
  have hr : coneRadius x y≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hd := (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne'
  simp only [retardedG,eulerianG,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul]
  field_simp

lemma retarded_electric_density_identity {f : Particle} {x y v E B : Vec} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t-coneRadius x y,y,v)) (hxy : x≠y)
    (heq : fderiv ℝ f (t-coneRadius x y,y,v)
      (1,velocity v,E+cross (velocity v) B)=0) (i : Fin 3) :
    ((coneRadius x y)^2)⁻¹*coneDirection x y i*f (t-coneRadius x y,y,v) +
      (coneDirection x y i-velocity v i)/coneRadius x y *
        fderiv ℝ f (t-coneRadius x y,y,v) (1,0,0) =
      f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
        physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
          (fderiv ℝ velocity v (E+cross (velocity v) B)) i -
      divergence (fun z => (retardedDensity f t x (z,v)*retardedG x (z,v) i) • velocity v) y -
      divergence (fun w => (retardedDensity f t x (y,w)*retardedG x (y,w) i) •
        (E+cross (velocity w) B)) v := by
  have hR := differentiableAt_retardedDensity hf hxy
  have hG := differentiableAt_retardedG (v:=v) hxy
  have hGi : DifferentiableAt ℝ (fun z : Phase => retardedG x z i) (y,v) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp (y,v) hG
  have hK := (contDiff_lorentz (k:=1) E B).differentiable (by simp) v
  have hdiv := phase_divergence_transport (u:=velocity v) (hR.mul hGi) hK
  rw [divergence_lorentz,mul_zero,add_zero,fderiv_mul hR hGi] at hdiv
  simp only [add_apply,smul_apply,smul_eq_mul] at hdiv
  rw [fderiv_vec_component_at hG i,fderiv_retardedG hxy] at hdiv
  have htr : fderiv ℝ (retardedDensity f t x) (y,v) (velocity v,E+cross (velocity v) B) =
      -(1-dot (coneDirection x y) (velocity v))*fderiv ℝ f (t-coneRadius x y,y,v) (1,0,0) :=
    retarded_transport_identity hf hxy heq
  rw [htr] at hdiv
  simp only [retardedDensity,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul] at hdiv
  have hgd := retardedG_deficit_component (v:=v) hxy i
  linear_combination hdiv - (fderiv ℝ f (t-coneRadius x y,y,v) (1,0,0))*hgd

lemma fderiv_cross_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F G : H → Vec} {z e : H} (hF : DifferentiableAt ℝ F z)
    (hG : DifferentiableAt ℝ G z) :
    fderiv ℝ (fun w => cross (F w) (G w)) z e =
      cross (fderiv ℝ F z e) (G z)+cross (F z) (fderiv ℝ G z e) := by
  have hi (A : H → Vec) (hA : DifferentiableAt ℝ A z) (i : Fin 3) :
      DifferentiableAt ℝ (fun w => A w i) z :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp z hA
  have hcross : DifferentiableAt ℝ (fun w => cross (F w) (G w)) z :=
    (contDiff_cross (k:=1)).differentiable (by simp) _ |>.comp z (hF.prodMk hG)
  have hmul (i j : Fin 3) : DifferentiableAt ℝ (fun w => F w i*G w j) z :=
    (hi F hF i).mul (hi G hG j)
  have hp (i j : Fin 3) : fderiv ℝ (fun w => F w i*G w j-F w j*G w i) z e =
      (fderiv ℝ F z e) i*G z j-(fderiv ℝ F z e) j*G z i +
      (F z i*(fderiv ℝ G z e) j-F z j*(fderiv ℝ G z e) i) := by
    rw [fderiv_fun_sub (hmul i j) (hmul j i),
      fderiv_fun_mul (hi F hF i) (hi G hG j),fderiv_fun_mul (hi F hF j) (hi G hG i)]
    simp only [sub_apply,add_apply,smul_apply,smul_eq_mul,fderiv_vec_component_at hF,
      fderiv_vec_component_at hG]
    ring
  ext i
  rw [← fderiv_vec_component_at hcross i]
  fin_cases i
  · exact hp 1 2
  · exact hp 2 0
  · exact hp 0 1

lemma fderiv_coneDirection_apply {x y u : Vec} (hxy : x≠y) :
    fderiv ℝ (coneDirection x) y u = (coneRadius x y)⁻¹ •
      (dot (coneDirection x y) u • coneDirection x y-u) := by
  apply fderiv_of_line_rvm (differentiableAt_coneDirection hxy)
  have hh := hasDerivAt_eulerian_direction (hasDerivAt_line_rvm y u)
    (by simpa only [zero_smul,add_zero] using hxy)
  convert hh using 1 <;> first | rfl | simp only [zero_smul,add_zero]

lemma eulerian_cross_direction {r : ℝ} {n u : Vec} (hr : r≠0)
    (hd : 1-dot n u≠0) :
    cross (r⁻¹ • (dot n u • n-u)) (eulerianG r n u) = (r^2)⁻¹ • cross n u := by
  ext i
  fin_cases i <;> dsimp [cross,eulerianG] <;> field_simp <;> ring

def retardedH (x : Vec) (z : Phase) : Vec := cross (coneDirection x z.1) (retardedG x z)

lemma differentiableAt_retardedH {x y v : Vec} (hxy : x≠y) :
    DifferentiableAt ℝ (retardedH x) (y,v) := by
  exact (contDiff_cross (k:=1)).differentiable (by simp) _ |>.comp
    (f:=fun z : Phase => (coneDirection x z.1,retardedG x z)) (y,v)
    (((differentiableAt_coneDirection hxy).comp (f:=Prod.fst) (y,v)
      differentiableAt_fst).prodMk (differentiableAt_retardedG hxy))

lemma fderiv_retardedH {x y v K : Vec} (hxy : x≠y) :
    fderiv ℝ (retardedH x) (y,v) (velocity v,K) =
      (1-dot (coneDirection x y) (velocity v)) • cross (coneDirection x y)
        (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
          (fderiv ℝ velocity v K)) +
      ((coneRadius x y)^2)⁻¹ • cross (coneDirection x y) (velocity v) := by
  have hn : DifferentiableAt ℝ (fun z : Phase => coneDirection x z.1) (y,v) :=
    (differentiableAt_coneDirection hxy).comp (f:=Prod.fst) (y,v) differentiableAt_fst
  have he : fderiv ℝ (fun z : Phase => coneDirection x z.1) (y,v) (velocity v,K) =
      (coneRadius x y)⁻¹ • (dot (coneDirection x y) (velocity v) • coneDirection x y-velocity v) := by
    have hfst : HasFDerivAt (Prod.fst : Phase → Vec) (ContinuousLinearMap.fst ℝ Vec Vec) (y,v) :=
      hasFDerivAt_fst
    have hd := (differentiableAt_coneDirection hxy).hasFDerivAt.comp (y,v) hfst
    have hh : fderiv ℝ (fun z : Phase => coneDirection x z.1) (y,v) (velocity v,K) =
        fderiv ℝ (coneDirection x) y (velocity v) := by
      convert congrArg (fun L : Phase →L[ℝ] Vec => L (velocity v,K)) hd.fderiv using 1 <;> rfl
    rw [hh,fderiv_coneDirection_apply hxy]
  change fderiv ℝ (fun z : Phase => cross (coneDirection x z.1) (retardedG x z)) (y,v) _ = _
  rw [fderiv_cross_apply hn (differentiableAt_retardedG hxy),he,
    fderiv_retardedG hxy]
  have hc := eulerian_cross_direction
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
    (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne'
  change cross _ (eulerianG _ _ _)+_=_
  change cross _ (eulerianG (coneRadius x y) (coneDirection x y) (velocity v))+_=_
  change cross ((coneRadius x y)⁻¹ • _) (eulerianG (coneRadius x y) _ _) = _ at hc
  rw [hc]
  ext i
  fin_cases i <;> dsimp [cross,coneRadius] <;> ring

lemma retardedH_deficit_component {x y v : Vec} (hxy : x≠y) (i : Fin 3) :
    (1-dot (coneDirection x y) (velocity v))*retardedH x (y,v) i =
      -(cross (coneDirection x y) (velocity v)) i/coneRadius x y := by
  have hr : coneRadius x y≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hd := (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne'
  fin_cases i <;> dsimp [retardedH,retardedG,eulerianG,cross] <;> field_simp <;> ring

lemma retarded_magnetic_density_identity {f : Particle} {x y v E B : Vec} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t-coneRadius x y,y,v)) (hxy : x≠y)
    (heq : fderiv ℝ f (t-coneRadius x y,y,v)
      (1,velocity v,E+cross (velocity v) B)=0) (i : Fin 3) :
    -((coneRadius x y)^2)⁻¹*cross (coneDirection x y) (velocity v) i*f (t-coneRadius x y,y,v) -
      cross (coneDirection x y) (velocity v) i/coneRadius x y *
        fderiv ℝ f (t-coneRadius x y,y,v) (1,0,0) =
      f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
        cross (coneDirection x y)
          (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
            (fderiv ℝ velocity v (E+cross (velocity v) B))) i -
      divergence (fun z => (retardedDensity f t x (z,v)*retardedH x (z,v) i) • velocity v) y -
      divergence (fun w => (retardedDensity f t x (y,w)*retardedH x (y,w) i) •
        (E+cross (velocity w) B)) v := by
  have hR := differentiableAt_retardedDensity hf hxy
  have hH := differentiableAt_retardedH (v:=v) hxy
  have hHi : DifferentiableAt ℝ (fun z : Phase => retardedH x z i) (y,v) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp (y,v) hH
  have hK := (contDiff_lorentz (k:=1) E B).differentiable (by simp) v
  have hdiv := phase_divergence_transport (u:=velocity v) (hR.mul hHi) hK
  rw [divergence_lorentz,mul_zero,add_zero,fderiv_mul hR hHi] at hdiv
  simp only [add_apply,smul_apply,smul_eq_mul] at hdiv
  rw [fderiv_vec_component_at hH i,fderiv_retardedH hxy] at hdiv
  have htr : fderiv ℝ (retardedDensity f t x) (y,v) (velocity v,E+cross (velocity v) B) =
      -(1-dot (coneDirection x y) (velocity v))*fderiv ℝ f (t-coneRadius x y,y,v) (1,0,0) :=
    retarded_transport_identity hf hxy heq
  rw [htr] at hdiv
  simp only [retardedDensity,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at hdiv
  have hhd := retardedH_deficit_component (v:=v) hxy i
  linear_combination hdiv - (fderiv ℝ f (t-coneRadius x y,y,v) (1,0,0))*hhd

def holeCutoff (ε : ℝ) (x : Vec) : ℝ := 1-ballCutoff (ε/2) (ε^2/8) x

lemma contDiff_holeCutoff (ε : ℝ) {k : ℕ∞} : ContDiff ℝ k (holeCutoff ε) :=
  contDiff_const.sub (contDiff_ballCutoff _ _)

lemma holeCutoff_zero {ε : ℝ} (hε : 0<ε) {x : Vec} (hx : ‖x‖<ε/4) :
    holeCutoff ε x=0 := by
  rw [holeCutoff,ballCutoff,Real.smoothTransition.one_of_one_le,sub_self]
  apply (le_div_iff₀ (by positivity : 0<ε^2/8)).mpr
  nlinarith [sq_nonneg (ε/4-‖x‖),norm_nonneg x]

lemma holeCutoff_one {ε : ℝ} (hε : 0<ε) {x : Vec} (hx : ε/2≤‖x‖) :
    holeCutoff ε x=1 := by
  rw [holeCutoff,ballCutoff,Real.smoothTransition.zero_of_nonpos,sub_zero]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  nlinarith [sq_nonneg (‖x‖-ε/2)]

lemma holeCutoff_eventually_one {ε : ℝ} (hε : 0<ε) {x : Vec} (hx : ε/2<‖x‖) :
    holeCutoff ε =ᶠ[𝓝 x] (fun _ => 1) := by
  have hn : {y : Vec | ε/2<‖y‖} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hx
  filter_upwards [hn] with y hy
  exact holeCutoff_one hε hy.le

lemma contDiff_holeCutoff_smul {ε : ℝ} {F : Vec → Vec} (hε : 0<ε)
    (hF : ∀ x≠0, ContDiffAt ℝ 1 F x) :
    ContDiff ℝ 1 (fun x => holeCutoff ε x • F x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have he : (fun x => holeCutoff ε x • F x) =ᶠ[𝓝 (0:Vec)] (fun _ => 0) := by
      filter_upwards [ball_mem_nhds (0:Vec) (by positivity : 0<ε/4)] with y hy
      rw [holeCutoff_zero hε (by simpa only [mem_ball_zero_iff] using hy),zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (contDiff_holeCutoff ε).contDiffAt.smul (hF x hx)

lemma divergence_congr_eventually {F G : Vec → Vec} {x : Vec} (h : F =ᶠ[𝓝 x] G) :
    divergence F x=divergence G x := by
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i))
    ((h.fun_comp (fun w : Vec => w i)).fderiv_eq (𝕜:=ℝ))

lemma divergence_holeCutoff {ε : ℝ} {F : Vec → Vec} {x : Vec} (hε : 0<ε)
    (hx : ε/2<‖x‖) :
    divergence (fun z => holeCutoff ε z • F z) x = divergence F x := by
  apply divergence_congr_eventually
  filter_upwards [holeCutoff_eventually_one hε hx] with y hy
  rw [hy,one_smul]

lemma divergence_annulus {ε R : ℝ} (hε : 0<ε) (hεR : ε≤R) {F : Vec → Vec}
    (hF : ∀ x≠0, ContDiffAt ℝ 1 F x) :
    (∫ x in ball (0:Vec) R \ ball (0:Vec) ε, divergence F x) =
      (∫ n : Sphere, R^2*dot n.1 (F (R • n.1)) ∂sphereMeasure) -
      (∫ n : Sphere, ε^2*dot n.1 (F (ε • n.1)) ∂sphereMeasure) := by
  let G : Vec → Vec := fun x => holeCutoff ε x • F x
  have hG := contDiff_holeCutoff_smul hε hF
  have hD : Continuous (divergence G) := continuous_divergence hG
  have hi : IntegrableOn (divergence G) (ball (0:Vec) R) :=
    (hD.continuousOn.integrableOn_compact (isCompact_closedBall (0:Vec) R)).mono_set ball_subset_closedBall
  have hd : (∫ x in ball (0:Vec) R \ ball (0:Vec) ε, divergence F x) =
      (∫ x in ball (0:Vec) R, divergence G x) - (∫ x in ball (0:Vec) ε, divergence G x) := by
    rw [← setIntegral_sdiff measurableSet_ball hi (ball_subset_ball hεR)]
    apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
    intro x hx
    apply (divergence_holeCutoff hε _).symm
    have hh : ε≤‖x‖ := by simpa only [mem_ball_zero_iff,not_lt] using hx.2
    linarith
  rw [hd,divergence_ball (hε.trans_le hεR) hG,divergence_ball hε hG]
  have hval (c : ℝ) (hc : ε≤c) (n : Sphere) : G (c • n.1)=F (c • n.1) := by
    dsimp [G]
    rw [holeCutoff_one hε,one_smul]
    have hn : ‖n.1‖=1 := sphere_norm n
    rw [norm_smul,Real.norm_of_nonneg (hε.le.trans hc),hn,mul_one]
    linarith
  congr 1 <;> apply integral_congr_ae <;> filter_upwards [] with n
  · change R^2*dot n.1 (G (R • n.1)) = _
    rw [hval R hεR]
  · change ε^2*dot n.1 (G (ε • n.1)) = _
    rw [hval ε le_rfl]



section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma contDiff_dot_pair {k : ℕ∞ω} :
    ContDiff ℝ k (fun z : Vec × Vec => dot z.1 z.2) := by
  unfold dot
  fun_prop

lemma contDiff_eulerianG_velocity {k : ℕ∞ω} {r : ℝ} {n : Vec}
    (hr : r≠0) (hn : ‖n‖=1) :
    ContDiff ℝ k (fun v => eulerianG r n (velocity v)) := by
  have hd : ContDiff ℝ k (fun v => 1-dot n (velocity v)) :=
    contDiff_const.sub (contDiff_dot_pair.comp (contDiff_const.prodMk contDiff_velocity))
  exact ((contDiff_const.mul hd).inv (fun v => mul_ne_zero hr (cone_denom_pos v n hn).ne')).smul
    (contDiff_const.sub contDiff_velocity)

lemma contDiff_retardedG_velocity {k : ℕ∞ω} {x y : Vec} (hxy : x≠y) :
    ContDiff ℝ k (fun v => retardedG x (y,v)) := by
  change ContDiff ℝ k (fun v => eulerianG (coneRadius x y) (coneDirection x y) (velocity v))
  have hr : coneRadius x y≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  exact contDiff_eulerianG_velocity hr (coneDirection_norm hxy)

lemma contDiff_retardedH_velocity {k : ℕ∞ω} {x y : Vec} (hxy : x≠y) :
    ContDiff ℝ k (fun v => retardedH x (y,v)) := by
  change ContDiff ℝ k (fun v => cross (coneDirection x y) (retardedG x (y,v)))
  exact contDiff_cross.comp ((contDiff_const (c:=coneDirection x y)).prodMk
    (contDiff_retardedG_velocity (k:=k) hxy))

lemma contDiff_particle_velocity_profile {s : Solution} {t : ℝ} (ht : 0≤t) (x : Vec)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) :
    ContDiff ℝ 1 (fun v => s.f (t,x,v)) := by
  apply contDiffOn_univ.mp
  exact hf.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
    (fun _ _ => ht)

lemma compactSupport_particle_velocity_profile {s : Solution} {t : ℝ} (ht : 0≤t) (x : Vec)
    (hc : CompactOnFiniteHorizons s) :
    HasCompactSupport (fun v => s.f (t,x,v)) := by
  obtain ⟨K,hK,hz⟩ := hc t ht
  apply compactSupport_of_zero_off (hK.image continuous_snd)
  intro v hv
  by_contra hne
  exact hv ⟨(x,v),hz t ⟨ht,le_rfl⟩ (subset_tsupport _ hne),rfl⟩

lemma integral_retarded_velocity_divergence_zero {f : Vec → ℝ} {G : Vec → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hG : ContDiff ℝ 1 G)
    (E B : Vec) :
    (∫ v : Vec, divergence (fun w => (f w*G w) • (E+cross (velocity w) B)) v)=0 := by
  apply integral_divergence_zero ((hf.mul hG).smul (contDiff_lorentz E B))
  exact (hc.mul_right).smul_right

lemma classical_retarded_electric_velocity_divergence {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0≤t-coneRadius x y) (i : Fin 3) :
    (∫ v : Vec, divergence (fun w =>
      (retardedDensity s.f t x (y,w)*retardedG x (y,w) i) •
      (s.E (t-coneRadius x y,y)+cross (velocity w) (s.B (t-coneRadius x y,y)))) v)=0 := by
  apply integral_retarded_velocity_divergence_zero
    (contDiff_particle_velocity_profile ht y hf)
    (compactSupport_particle_velocity_profile ht y hc)
  exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp
    (contDiff_retardedG_velocity hxy)

lemma classical_retarded_magnetic_velocity_divergence {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0≤t-coneRadius x y) (i : Fin 3) :
    (∫ v : Vec, divergence (fun w =>
      (retardedDensity s.f t x (y,w)*retardedH x (y,w) i) •
      (s.E (t-coneRadius x y,y)+cross (velocity w) (s.B (t-coneRadius x y,y)))) v)=0 := by
  apply integral_retarded_velocity_divergence_zero
    (contDiff_particle_velocity_profile ht y hf)
    (compactSupport_particle_velocity_profile ht y hc)
  exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp
    (contDiff_retardedH_velocity hxy)

lemma integrable_divergence_compact {F : Vec → Vec}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) : Integrable (divergence F) := by
  apply (continuous_divergence hF).integrable_of_hasCompactSupport
  change HasCompactSupport (∑ i : Fin 3, fun x => spatialPartial (fun y => F y i) x i)
  apply HasCompactSupport.finset_sum
  intro i _
  exact (hc.comp_left (g:=fun v : Vec => v i) (by simp)).fderiv_apply ℝ (basis i)

lemma divergence_integral_uniform_support
    {U : Set Vec} {K : Set Vec} {F : Phase → Vec} {y : Vec}
    (hU : IsOpen U) (hK : IsCompact K) (hy : y ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hz : ∀ x ∈ U, ∀ v ∉ K, F (x,v)=0) :
    divergence (fun z => ∫ v : Vec, F (z,v)) y =
      ∫ v : Vec, divergence (fun z => F (z,v)) y := by
  have hdiff (v : Vec) : DifferentiableAt ℝ F (y,v) :=
    (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy,mem_univ _⟩)).differentiableAt (by simp)
  have hi := (hasFDerivAt_integral_uniform_support hU hK hy hF hz).differentiableAt
  have hc : Continuous (fun v : Vec => fderiv ℝ F (y,v)) :=
    (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hy,mem_univ _⟩)
  have hcs := compactSupport_param_fderiv hU hK hy hz
  have hint (i : Fin 3) : Integrable (fun v : Vec => fderiv ℝ F (y,v) (basis i,0)) :=
    (hc.clm_apply continuous_const).integrable_of_hasCompactSupport
      (hcs.comp_left (g:=fun L : Phase →L[ℝ] Vec => L (basis i,0)) (by simp))
  have hinti (i : Fin 3) : Integrable (fun v : Vec => (fderiv ℝ F (y,v) (basis i,0)) i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp (hint i)
  have hslice (v e : Vec) : fderiv ℝ (fun z => F (z,v)) y e = fderiv ℝ F (y,v) (e,0) := by
    have hm : HasFDerivAt (fun z : Vec => (z,v))
        ((ContinuousLinearMap.id ℝ Vec).prod 0) y :=
      (hasFDerivAt_id y).prodMk (hasFDerivAt_const v y)
    have hh := (hdiff v).hasFDerivAt.comp (f:=fun z : Vec => (z,v)) y hm
    convert congrArg (fun L : Vec →L[ℝ] Vec => L e) hh.fderiv using 1 <;> rfl
  unfold divergence spatialPartial
  simp_rw [fderiv_vec_component_at hi]
  simp_rw [fderiv_integral_uniform_support_apply hU hK hy hF hz,
    integral_vec_apply (hint _)]
  rw [← integral_finsetSum _ (fun i _ => hinti i)]
  apply integral_congr_ae
  filter_upwards [] with v
  apply Finset.sum_congr rfl
  intro i _
  have hsliceD : DifferentiableAt ℝ (fun z => F (z,v)) y :=
    (hdiff v).comp y (differentiableAt_id.prodMk (differentiableAt_const v))
  rw [fderiv_vec_component_at hsliceD,hslice]

lemma contDiffAt_coneRadius {k : ℕ∞ω} {x y : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (coneRadius x) y :=
  (contDiffAt_const.sub contDiffAt_id).norm ℝ (sub_ne_zero.mpr hxy)

lemma contDiffAt_coneDirection {k : ℕ∞ω} {x y : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (coneDirection x) y :=
  ((contDiffAt_coneRadius hxy).inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))).smul
    (contDiffAt_const.sub contDiffAt_id)

lemma contDiffAt_retardedG {k : ℕ∞ω} {x y v : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (retardedG x) (y,v) := by
  have hr : ContDiffAt ℝ k (fun z : Phase => coneRadius x z.1) (y,v) :=
    (contDiffAt_coneRadius (k:=k) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hn : ContDiffAt ℝ k (fun z : Phase => coneDirection x z.1) (y,v) :=
    (contDiffAt_coneDirection (k:=k) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hu : ContDiffAt ℝ k (fun z : Phase => velocity z.2) (y,v) :=
    contDiff_velocity.contDiffAt.comp (y,v) contDiffAt_snd
  have hd : ContDiffAt ℝ k (fun z : Phase => 1-dot (coneDirection x z.1) (velocity z.2)) (y,v) :=
    contDiffAt_const.sub (contDiff_dot_pair.contDiffAt.comp (y,v) (hn.prodMk hu))
  exact ((hr.mul hd).inv (mul_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
    (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne')).smul (hn.sub hu)

lemma contDiffAt_retardedH {k : ℕ∞ω} {x y v : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (retardedH x) (y,v) :=
  contDiff_cross.contDiffAt.comp (y,v)
    (((contDiffAt_coneDirection (k:=k) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst).prodMk
      (contDiffAt_retardedG hxy))

lemma contDiffAt_retardedDensity {k : ℕ∞ω} {f : Particle} {x y v : Vec} {t : ℝ}
    (hf : ContDiffAt ℝ k f (t-coneRadius x y,y,v)) (hxy : x≠y) :
    ContDiffAt ℝ k (retardedDensity f t x) (y,v) := by
  have hr : ContDiffAt ℝ k (fun z : Phase => coneRadius x z.1) (y,v) :=
    (contDiffAt_coneRadius (k:=k) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hm : ContDiffAt ℝ k (fun z : Phase => (t-coneRadius x z.1,z)) (y,v) :=
    ((contDiffAt_const (c:=t)).sub hr).prodMk contDiffAt_id
  exact hf.comp (f:=fun z : Phase => (t-coneRadius x z.1,z)) (y,v) hm

lemma particle_contDiffAt_positive {k : ℕ∞ω} {f : Particle}
    (hf : ContDiffOn ℝ k f particleHalfSpace) {t : ℝ} (ht : 0<t) (x v : Vec) :
    ContDiffAt ℝ k f (t,x,v) := by
  have hn : particleHalfSpace ∈ 𝓝 (t,x,v) :=
    mem_of_superset ((isOpen_lt continuous_const
      (continuous_fst : Continuous (Prod.fst : ℝ × Phase → ℝ))).mem_nhds ht)
      (fun z hz => show 0≤z.1 from hz.le)
  exact (hf _ ht.le).contDiffAt hn

def retardedSpaceDomain (t : ℝ) (x : Vec) : Set Vec :=
  {y | x≠y ∧ 0<t-coneRadius x y}

lemma isOpen_retardedSpaceDomain (t : ℝ) (x : Vec) : IsOpen (retardedSpaceDomain t x) := by
  have h₁ : IsOpen {y : Vec | y≠x} := isOpen_ne
  have h₂ : IsOpen {y : Vec | 0<t-coneRadius x y} :=
    isOpen_lt continuous_const (continuous_const.sub ((continuous_const.sub continuous_id).norm))
  convert h₁.inter h₂ using 1
  ext y
  simp only [retardedSpaceDomain,mem_ofPred_eq,mem_inter_iff,ne_comm]

lemma retarded_local_data {s : Solution} (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t : ℝ} (ht : 0≤t) (x : Vec) :
    ∃ K : Set Vec, IsCompact K ∧
      ContDiffOn ℝ 1 (retardedDensity s.f t x) (retardedSpaceDomain t x ×ˢ univ) ∧
      ∀ y ∈ retardedSpaceDomain t x, ∀ v ∉ K, retardedDensity s.f t x (y,v)=0 := by
  obtain ⟨K,hK,hz⟩ := hc t ht
  refine ⟨Prod.snd '' K,hK.image continuous_snd,?_,?_⟩
  · intro z hz
    exact (contDiffAt_retardedDensity
      (particle_contDiffAt_positive hf hz.1.2 z.1 z.2) hz.1.1).contDiffWithinAt
  · intro y hy v hv
    by_contra hne
    have htime : t-coneRadius x y ∈ Icc 0 t :=
      ⟨hy.2.le,sub_le_self _ (norm_nonneg _)⟩
    exact hv ⟨(y,v),hz _ htime (subset_tsupport _ hne),rfl⟩

lemma integrable_spatial_divergence_uniform_support
    {U : Set Vec} {K : Set Vec} {F : Phase → Vec} {y : Vec}
    (hU : IsOpen U) (hK : IsCompact K) (hy : y ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hz : ∀ x ∈ U, ∀ v ∉ K, F (x,v)=0) :
    Integrable (fun v : Vec => divergence (fun z => F (z,v)) y) := by
  have hc : Continuous (fun v : Vec => fderiv ℝ F (y,v)) :=
    (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hy,mem_univ _⟩)
  have hcs := compactSupport_param_fderiv hU hK hy hz
  have hint (i : Fin 3) : Integrable (fun v : Vec => (fderiv ℝ F (y,v) (basis i,0)) i) := by
    apply (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp
    exact (hc.clm_apply continuous_const).integrable_of_hasCompactSupport
      (hcs.comp_left (g:=fun L : Phase →L[ℝ] Vec => L (basis i,0)) (by simp))
  apply (integrable_finsetSum Finset.univ (fun i _ => hint i)).congr
  filter_upwards [] with v
  unfold divergence spatialPartial
  apply Finset.sum_congr rfl
  intro i _
  have hd : DifferentiableAt ℝ F (y,v) :=
    (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy,mem_univ _⟩)).differentiableAt (by simp)
  have hm : HasFDerivAt (fun z : Vec => (z,v)) ((ContinuousLinearMap.id ℝ Vec).prod 0) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const v y)
  have hh := hd.hasFDerivAt.comp (f:=fun z : Vec => (z,v)) y hm
  have hslice : DifferentiableAt ℝ (fun z => F (z,v)) y := hh.differentiableAt
  rw [fderiv_vec_component_at hslice i]
  change (fderiv ℝ F (y,v) (basis i,0)) i = _
  rw [show fderiv ℝ (fun z => F (z,v)) y =
      (fderiv ℝ F (y,v)).comp ((ContinuousLinearMap.id ℝ Vec).prod 0) from hh.fderiv]
  rfl

lemma classical_retarded_flux_calculus {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0<t-coneRadius x y)
    {G : Phase → ℝ}
    (hG : ∀ z ∈ retardedSpaceDomain t x, ∀ v, ContDiffAt ℝ 1 G (z,v)) :
    Integrable (fun v : Vec => divergence
      (fun z => (retardedDensity s.f t x (z,v)*G (z,v)) • velocity v) y) ∧
    divergence (fun z => ∫ v : Vec, (retardedDensity s.f t x (z,v)*G (z,v)) • velocity v) y =
      ∫ v : Vec, divergence (fun z => (retardedDensity s.f t x (z,v)*G (z,v)) • velocity v) y := by
  have ht0 : 0≤t := by have hr := norm_nonneg (x-y); change 0<t-‖x-y‖ at ht; linarith
  obtain ⟨K,hK,hF,hz⟩ := retarded_local_data hf hc ht0 x
  have hG' : ContDiffOn ℝ 1 G (retardedSpaceDomain t x ×ˢ univ) :=
    fun z hz => (hG z.1 hz.1 z.2).contDiffWithinAt
  have hcF : ContDiffOn ℝ 1
      (fun z : Phase => (retardedDensity s.f t x z*G z) • velocity z.2)
      (retardedSpaceDomain t x ×ˢ univ) :=
    (hF.mul hG').smul ((contDiff_velocity.comp contDiff_snd).contDiffOn)
  have hzero : ∀ z ∈ retardedSpaceDomain t x, ∀ v ∉ K,
      (retardedDensity s.f t x (z,v)*G (z,v)) • velocity v=0 := by
    intro z hz' v hv
    rw [hz z hz' v hv,zero_mul,zero_smul]
  have hU := isOpen_retardedSpaceDomain t x
  have hy : y ∈ retardedSpaceDomain t x := ⟨hxy,ht⟩
  have hi := integrable_spatial_divergence_uniform_support
    (F := fun z : Phase => (retardedDensity s.f t x z*G z) • velocity z.2)
    hU hK hy hcF hzero
  have he := divergence_integral_uniform_support
    (F := fun z : Phase => (retardedDensity s.f t x z*G z) • velocity z.2)
    hU hK hy hcF hzero
  exact ⟨hi,he⟩

lemma continuous_physicalElectricKernel_velocity {r : ℝ} {n : Vec}
    (hr : r≠0) (hn : ‖n‖=1) (E B : Vec) :
    Continuous (fun v => physicalElectricKernel r n (velocity v)
      (fderiv ℝ velocity v (E+cross (velocity v) B))) := by
  have hu : Continuous velocity := (contDiff_velocity (k:=1)).continuous
  have hb : Continuous (fun v => fderiv ℝ velocity v (E+cross (velocity v) B)) :=
    ((contDiff_velocity (k:=1)).continuous_fderiv (by simp)).clm_apply
      (contDiff_lorentz (k:=1) E B).continuous
  have hd : Continuous (fun v => 1-dot n (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_const.prodMk hu))
  have hd0 (v : Vec) : 1-dot n (velocity v)≠0 := (cone_denom_pos v n hn).ne'
  have hnum : Continuous (fun v => 1-dot (velocity v) (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (hu.prodMk hu))
  have hnb : Continuous (fun v => dot n (fderiv ℝ velocity v (E+cross (velocity v) B))) :=
    (contDiff_dot_pair (k:=1)).continuous.comp (continuous_const.prodMk hb)
  exact ((hnum.div (continuous_const.mul (hd.pow 3)) (fun v => mul_ne_zero (pow_ne_zero 2 hr)
      (pow_ne_zero 3 (hd0 v)))).smul (continuous_const.sub hu)).add
    (((continuous_const.mul (hd.pow 3)).inv₀ (fun v => mul_ne_zero hr (pow_ne_zero 3 (hd0 v)))).smul
      ((hnb.smul (continuous_const.sub hu)).sub (hd.smul hb)))

lemma classical_retarded_integral_identity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0<t-coneRadius x y)
    {G : Phase → ℝ} {C L : Vec → ℝ}
    (hG : ∀ z ∈ retardedSpaceDomain t x, ∀ v, ContDiffAt ℝ 1 G (z,v))
    (hC : Continuous C)
    (heq : ∀ v, L v = retardedDensity s.f t x (y,v)*C v -
      divergence (fun z => (retardedDensity s.f t x (z,v)*G (z,v)) • velocity v) y -
      divergence (fun w => (retardedDensity s.f t x (y,w)*G (y,w)) •
        (s.E (t-coneRadius x y,y)+cross (velocity w) (s.B (t-coneRadius x y,y)))) v) :
    (∫ v : Vec, L v) = (∫ v : Vec, retardedDensity s.f t x (y,v)*C v) -
      divergence (fun z => ∫ v : Vec, (retardedDensity s.f t x (z,v)*G (z,v)) • velocity v) y := by
  have hfp := contDiff_particle_velocity_profile ht.le y hf
  have hfcp := compactSupport_particle_velocity_profile ht.le y hc
  have hGp : ContDiff ℝ 1 (fun v => G (y,v)) := by
    rw [contDiff_iff_contDiffAt]
    intro v
    exact (hG y ⟨hxy,ht⟩ v).comp (f:=fun w : Vec => (y,w)) v
      (contDiffAt_const.prodMk contDiffAt_id)
  have hcv : Integrable (fun v : Vec => retardedDensity s.f t x (y,v)*C v) :=
    (hfp.continuous.mul hC).integrable_of_hasCompactSupport hfcp.mul_right
  obtain ⟨hsi,hse⟩ := classical_retarded_flux_calculus hf hc hxy ht hG
  have hvg : ContDiff ℝ 1 (fun w => (retardedDensity s.f t x (y,w)*G (y,w)) •
      (s.E (t-coneRadius x y,y)+cross (velocity w) (s.B (t-coneRadius x y,y)))) :=
    (hfp.mul hGp).smul (contDiff_lorentz _ _)
  have hvcp : HasCompactSupport (fun w => (retardedDensity s.f t x (y,w)*G (y,w)) •
      (s.E (t-coneRadius x y,y)+cross (velocity w) (s.B (t-coneRadius x y,y)))) :=
    hfcp.mul_right.smul_right
  have hsub := integral_sub (hcv.sub hsi) (integrable_divergence_compact hvg hvcp)
  have hsub' := integral_sub hcv hsi
  simp only [Pi.sub_apply] at hsub hsub'
  simp_rw [heq]
  rw [hsub,hsub',integral_divergence_zero hvg hvcp,sub_zero,hse]

lemma classical_retarded_electric_integral_identity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (heq : Equations s) {x y : Vec} {t : ℝ}
    (hxy : x≠y) (ht : 0<t-coneRadius x y) (i : Fin 3) :
    (∫ v : Vec, ((coneRadius x y)^2)⁻¹*coneDirection x y i*s.f (t-coneRadius x y,y,v) +
      (coneDirection x y i-velocity v i)/coneRadius x y *
        fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) =
      (∫ v : Vec, s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
        physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
          (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
            cross (velocity v) (s.B (t-coneRadius x y,y)))) i) -
      divergence (fun z => ∫ v : Vec,
        (retardedDensity s.f t x (z,v)*retardedG x (z,v) i) • velocity v) y := by
  have hG : ∀ z ∈ retardedSpaceDomain t x, ∀ v,
      ContDiffAt ℝ 1 (fun z => retardedG x z i) (z,v) := by
    intro z hz v
    exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp (z,v)
      (contDiffAt_retardedG hz.1)
  have hu : Continuous velocity := (contDiff_velocity (k:=1)).continuous
  have hd : Continuous (fun v => 1-dot (coneDirection x y) (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_const.prodMk hu))
  have hk := continuous_physicalElectricKernel_velocity
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)) (coneDirection_norm hxy)
    (s.E (t-coneRadius x y,y)) (s.B (t-coneRadius x y,y))
  have hki : Continuous (fun v => physicalElectricKernel (coneRadius x y) (coneDirection x y)
      (velocity v) (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
        cross (velocity v) (s.B (t-coneRadius x y,y)))) i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp hk
  have hid := classical_retarded_integral_identity
    (L := fun v => ((coneRadius x y)^2)⁻¹*coneDirection x y i*s.f (t-coneRadius x y,y,v) +
      (coneDirection x y i-velocity v i)/coneRadius x y *
        fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) hf hc hxy ht hG (hd.mul hki)
  simp only [retardedDensity,mul_assoc,Pi.mul_apply] at hid ⊢
  apply hid
  intro v
  have hf' := particle_differentiableAt_positive hf ht y v
  have hv : fderiv ℝ s.f (t-coneRadius x y,y,v)
      (1,velocity v,s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y)))=0 := by
    simpa only [fderiv_particleBySpacetime hf'] using particle_spacetime_vlasov hf heq ht y v
  simpa only [retardedDensity,mul_assoc] using retarded_electric_density_identity hf' hxy hv i

lemma classical_retarded_magnetic_integral_identity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (heq : Equations s) {x y : Vec} {t : ℝ}
    (hxy : x≠y) (ht : 0<t-coneRadius x y) (i : Fin 3) :
    (∫ v : Vec, -((coneRadius x y)^2)⁻¹*cross (coneDirection x y) (velocity v) i*s.f (t-coneRadius x y,y,v) -
      cross (coneDirection x y) (velocity v) i/coneRadius x y *
        fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) =
      (∫ v : Vec, s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
        cross (coneDirection x y) (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
          (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
            cross (velocity v) (s.B (t-coneRadius x y,y))))) i) -
      divergence (fun z => ∫ v : Vec,
        (retardedDensity s.f t x (z,v)*retardedH x (z,v) i) • velocity v) y := by
  have hG : ∀ z ∈ retardedSpaceDomain t x, ∀ v,
      ContDiffAt ℝ 1 (fun z => retardedH x z i) (z,v) := by
    intro z hz v
    exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp (z,v)
      (contDiffAt_retardedH hz.1)
  have hu : Continuous velocity := (contDiff_velocity (k:=1)).continuous
  have hd : Continuous (fun v => 1-dot (coneDirection x y) (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_const.prodMk hu))
  have hk := continuous_physicalElectricKernel_velocity
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)) (coneDirection_norm hxy)
    (s.E (t-coneRadius x y,y)) (s.B (t-coneRadius x y,y))
  have hkc : Continuous (fun v => cross (coneDirection x y)
      (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
          cross (velocity v) (s.B (t-coneRadius x y,y)))))) :=
    (contDiff_cross (k:=1)).continuous.comp (continuous_const.prodMk hk)
  have hki : Continuous (fun v => cross (coneDirection x y)
      (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
          cross (velocity v) (s.B (t-coneRadius x y,y))))) i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp hkc
  have hid := classical_retarded_integral_identity
    (L := fun v => -((coneRadius x y)^2)⁻¹*cross (coneDirection x y) (velocity v) i*s.f (t-coneRadius x y,y,v) -
      cross (coneDirection x y) (velocity v) i/coneRadius x y *
        fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) hf hc hxy ht hG (hd.mul hki)
  simp only [retardedDensity,mul_assoc,Pi.mul_apply] at hid ⊢
  apply hid
  intro v
  have hf' := particle_differentiableAt_positive hf ht y v
  have hv : fderiv ℝ s.f (t-coneRadius x y,y,v)
      (1,velocity v,s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y)))=0 := by
    simpa only [fderiv_particleBySpacetime hf'] using particle_spacetime_vlasov hf heq ht y v
  simpa only [retardedDensity,mul_assoc] using retarded_magnetic_density_identity hf' hxy hv i

lemma dirD_integral_sphere {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [ProperSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W} (hF : ContDiff ℝ 1 F) (e p : H) :
    dirD (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) e p =
      ∫ n : Sphere, dirD F (e,0) (p,n.1) ∂sphereMeasure := by
  have hc : Continuous (fun n : Sphere => (fderiv ℝ F (p,n.1)).comp
      (ContinuousLinearMap.inl ℝ H Vec)) :=
    ((hF.continuous_fderiv (by simp)).comp
      (continuous_const.prodMk continuous_subtype_val)).clm_comp continuous_const
  unfold dirD
  rw [(hasFDerivAt_integral_sphere hF p).fderiv,
    ContinuousLinearMap.integral_apply (hc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) e]
  rfl

def radiusWaveKernel (ρ : ℝ × Vec → ℝ) (z : (ℝ × Vec) × ℝ) : ℝ :=
  (4*Real.pi)⁻¹*z.2*(∫ n : Sphere, ρ (z.1.1-z.2,z.1.2+z.2 • n.1) ∂sphereMeasure)

lemma sourceWave_eq_radius (ρ : ℝ × Vec → ℝ) : sourceWave ρ=volterra (radiusWaveKernel ρ) := by
  funext p
  have hh := intervalIntegral.integral_comp_sub_left (fun r => radiusWaveKernel ρ (p,r))
    (a:=0) (b:=p.1) p.1
  simpa only [sourceWave,volterra,sourceWaveKernel,waveK,sphereSum,radiusWaveKernel,
    sub_self,sub_zero,sub_sub_cancel,mul_assoc] using hh

lemma contDiff_radiusWaveKernel {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (radiusWaveKernel ρ) := by
  have hi : ContDiff ℝ ∞ (fun z : ((ℝ × Vec) × ℝ) × Vec =>
      ρ (z.1.1.1-z.1.2,z.1.1.2+z.1.2 • z.2)) := by
    apply hρ.comp
    exact ((contDiff_fst.comp (contDiff_fst.comp contDiff_fst)).sub
      (contDiff_snd.comp contDiff_fst)).prodMk
      ((contDiff_snd.comp (contDiff_fst.comp contDiff_fst)).add
        ((contDiff_snd.comp contDiff_fst).smul contDiff_snd))
  exact (contDiff_const.mul contDiff_snd).mul (contDiff_integral_sphere hi)

lemma dirD_radius_average {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (e p : ℝ × Vec) (r : ℝ) :
    dirD (fun z : ℝ × Vec => ∫ n : Sphere, ρ (z.1-r,z.2+r • n.1) ∂sphereMeasure) e p =
      ∫ n : Sphere, dirD ρ e (p.1-r,p.2+r • n.1) ∂sphereMeasure := by
  let F : (ℝ × Vec) × Vec → ℝ := fun z => ρ (z.1.1-r,z.1.2+r • z.2)
  have hF : ContDiff ℝ 1 F := hρ.of_le (by simp) |>.comp
    (((contDiff_fst.comp contDiff_fst).sub contDiff_const).prodMk
      ((contDiff_snd.comp contDiff_fst).add (contDiff_snd.const_smul r)))
  rw [show (fun z : ℝ × Vec => ∫ n : Sphere, ρ (z.1-r,z.2+r • n.1) ∂sphereMeasure)=
      (fun z => ∫ n : Sphere, F (z,n.1) ∂sphereMeasure) from rfl,dirD_integral_sphere hF]
  apply integral_congr_ae
  apply ae_of_all
  intro n
  have hi := ((hasFDerivAt_fst (𝕜:=ℝ) (p:=(p,n.1))).fst.sub_const r).prodMk
    (((hasFDerivAt_fst (𝕜:=ℝ) (p:=(p,n.1))).snd).add
      ((hasFDerivAt_snd (𝕜:=ℝ) (p:=(p,n.1))).const_smul r))
  have hd := (hρ.differentiable (by simp) (p.1-r,p.2+r • n.1)).hasFDerivAt.comp (p,n.1) hi
  change HasFDerivAt F _ (p,n.1) at hd
  change (fderiv ℝ F (p,n.1)) (e,0) = (fderiv ℝ ρ (p.1-r,p.2+r • n.1)) e
  rw [hd.fderiv]
  simp

lemma dirD_radiusWaveKernel {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (e p : ℝ × Vec) (r : ℝ) :
    dirD (radiusWaveKernel ρ) (e,0) (p,r)=radiusWaveKernel (dirD ρ e) (p,r) := by
  rw [← dirD_prod_left ((contDiff_radiusWaveKernel hρ).differentiable (by simp))]
  have hA : ContDiff ℝ ∞ (fun z : ℝ × Vec => ∫ n : Sphere,
      ρ (z.1-r,z.2+r • n.1) ∂sphereMeasure) :=
    contDiff_integral_sphere (hρ.comp
      (((contDiff_fst.comp contDiff_fst).sub contDiff_const).prodMk
        ((contDiff_snd.comp contDiff_fst).add (contDiff_snd.const_smul r))))
  change dirD (fun z : ℝ × Vec => ((4*Real.pi)⁻¹*r)*
    (∫ n : Sphere, ρ (z.1-r,z.2+r • n.1) ∂sphereMeasure)) e p = _
  unfold dirD
  rw [fderiv_const_mul (hA.differentiable (by simp) p)]
  change ((4*Real.pi)⁻¹*r)*dirD (fun z : ℝ × Vec =>
    ∫ n : Sphere, ρ (z.1-r,z.2+r • n.1) ∂sphereMeasure) e p = _
  rw [dirD_radius_average hρ]
  rfl

lemma dirD_sourceWave {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) (e p : ℝ × Vec) :
    dirD (sourceWave ρ) e p = e.1*waveK (fun y => ρ (0,y)) p + sourceWave (dirD ρ e) p := by
  rw [sourceWave_eq_radius ρ,dirD_volterra (contDiff_radiusWaveKernel hρ)]
  have he : dirD (radiusWaveKernel ρ) (e,0)=radiusWaveKernel (dirD ρ e) := by
    funext z
    exact dirD_radiusWaveKernel hρ e z.1 z.2
  rw [he,← sourceWave_eq_radius]
  simp only [radiusWaveKernel,waveK,sphereSum,sub_self,mul_assoc]

lemma electricPotentialComponent_source {ρ : ℝ × Vec → ℝ} {j : Field}
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j) (i : Fin 3) (p : ℝ × Vec) :
    electricPotentialComponent ρ j i p =
      -sourceWave (dirD ρ (0,basis i)) p -
        (waveK (fun y => j (0,y) i) p + sourceWave (dirD (fun z => j z i) (1,0)) p) := by
  unfold electricPotentialComponent
  rw [dirD_sourceWave hρ,dirD_sourceWave (contDiff_component hj i)]
  simp

lemma magneticPotentialComponent_source {j : Field} (hj : ContDiff ℝ ∞ j)
    (i : Fin 3) (p : ℝ × Vec) :
    magneticPotentialComponent j i p =
      sourceWave (dirD (fun z => j z (curlB i)) (0,basis (curlA i))) p -
      sourceWave (dirD (fun z => j z (curlA i)) (0,basis (curlB i))) p := by
  unfold magneticPotentialComponent
  rw [dirD_sourceWave (contDiff_component hj _),dirD_sourceWave (contDiff_component hj _)]
  simp

lemma ballCutoff_one {R ε : ℝ} (hε : 0<ε) {x : Vec}
    (hx : ε≤R^2-‖x‖^2) : ballCutoff R ε x=1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ hε).mpr (by simpa using hx)

lemma ballCutoff_eventually_one {R ε : ℝ} (hε : 0<ε) {x : Vec}
    (hx : ε<R^2-‖x‖^2) : ballCutoff R ε =ᶠ[𝓝 x] (fun _ => 1) := by
  filter_upwards [(isOpen_lt continuous_const (continuous_const.sub (continuous_norm.pow 2))).mem_nhds hx]
    with y hy
  exact ballCutoff_one hε hy.le

lemma divergence_annulus_local {ε R T : ℝ} (hε : 0<ε) (hεR : ε≤R) (hRT : R<T)
    {F : Vec → Vec} (hF : ∀ x, 0<‖x‖ → ‖x‖<T → ContDiffAt ℝ 1 F x) :
    (∫ x in ball (0:Vec) R \ ball (0:Vec) ε, divergence F x) =
      (∫ n : Sphere, R^2*dot n.1 (F (R • n.1)) ∂sphereMeasure) -
      (∫ n : Sphere, ε^2*dot n.1 (F (ε • n.1)) ∂sphereMeasure) := by
  let C := (R+T)/2
  let δ := C^2-R^2
  have hR : 0<R := hε.trans_le hεR
  have hRC : R<C := by dsimp [C]; linarith
  have hCT : C<T := by dsimp [C]; linarith
  have hC : 0<C := hR.trans hRC
  have hδ : 0<δ := by dsimp [δ]; nlinarith
  let G : Vec → Vec := fun x => ballCutoff C δ x • F x
  have hG : ∀ x≠0, ContDiffAt ℝ 1 G x := by
    intro x hx
    by_cases hxt : ‖x‖<T
    · exact (contDiff_ballCutoff C δ).contDiffAt.smul (hF x (norm_pos_iff.mpr hx) hxt)
    · have hcx : C<‖x‖ := hCT.trans_le (not_lt.mp hxt)
      have he : G =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hcx] with y hy
        dsimp [G]
        rw [ballCutoff_zero hC.le hδ (by simpa only [mem_closedBall_zero_iff,not_le] using hy),zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  have hD : ∀ x ∈ ball (0:Vec) R, divergence G x=divergence F x := by
    intro x hx
    have hxR : ‖x‖<R := by simpa only [mem_ball_zero_iff] using hx
    apply divergence_congr_eventually
    filter_upwards [ballCutoff_eventually_one hδ (show δ<C^2-‖x‖^2 by
      dsimp [δ]; nlinarith [norm_nonneg x])] with y hy
    dsimp [G]
    rw [hy,one_smul]
  have hV (c : ℝ) (hc : 0≤c) (hcR : c≤R) (n : Sphere) : G (c • n.1)=F (c • n.1) := by
    have hn : ‖c • n.1‖=c := by rw [norm_smul,Real.norm_of_nonneg hc,sphere_norm,mul_one]
    dsimp [G]
    rw [ballCutoff_one hδ (by rw [hn]; dsimp [δ]; nlinarith),one_smul]
  rw [setIntegral_congr_fun (g:=divergence G) (measurableSet_ball.diff measurableSet_ball)
    (fun x hx => (hD x hx.1).symm),divergence_annulus hε hεR hG]
  congr 1 <;> apply integral_congr_ae <;> filter_upwards [] with n
  · rw [hV R hR.le le_rfl]
  · rw [hV ε hε.le hεR]

lemma integral_annulus_tendsto {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {R : ℝ} (hF : IntegrableOn F (ball (0:Vec) R)) :
    Tendsto (fun ε : ℝ => ∫ x in ball (0:Vec) R \ ball (0:Vec) ε, F x)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ x in ball (0:Vec) R, F x)) := by
  have ht : Tendsto (fun ε : ℝ => ∫ x in ball (0:Vec) R,
      (ball (0:Vec) ε)ᶜ.indicator F x) (𝓝[>] (0:ℝ))
      (𝓝 (∫ x in ball (0:Vec) R, F x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖)
    · exact Eventually.of_forall (fun ε => hF.aestronglyMeasurable.indicator measurableSet_ball.compl)
    · exact Eventually.of_forall (fun ε => ae_of_all _ (fun x => norm_indicator_le_norm_self _ _))
    · exact hF.norm
    · filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:Vec))] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT (norm_pos_iff.mpr hx)] with ε hε
      symm
      exact indicator_of_mem (show x ∈ (ball (0:Vec) ε)ᶜ by
        simp only [mem_compl_iff,mem_ball_zero_iff]; exact not_lt_of_ge hε.2.le) F
  simpa only [setIntegral_indicator measurableSet_ball.compl,sdiff_eq_compl_inter,inter_comm] using ht

lemma divergence_ball_singular {R T : ℝ} (hR : 0<R) (hRT : R<T)
    {F : Vec → Vec} (hF : ∀ x, 0<‖x‖ → ‖x‖<T → ContDiffAt ℝ 1 F x)
    (hi : IntegrableOn (divergence F) (ball (0:Vec) R))
    (hzero : Tendsto (fun ε : ℝ => ∫ n : Sphere,
      ε^2*dot n.1 (F (ε • n.1)) ∂sphereMeasure) (𝓝[>] (0:ℝ)) (𝓝 0)) :
    (∫ x in ball (0:Vec) R, divergence F x) =
      ∫ n : Sphere, R^2*dot n.1 (F (R • n.1)) ∂sphereMeasure := by
  have he : (fun ε : ℝ => ∫ x in ball (0:Vec) R \ ball (0:Vec) ε, divergence F x) =ᶠ[𝓝[>] 0]
      (fun ε => (∫ n : Sphere, R^2*dot n.1 (F (R • n.1)) ∂sphereMeasure) -
        (∫ n : Sphere, ε^2*dot n.1 (F (ε • n.1)) ∂sphereMeasure)) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with ε hε
    exact divergence_annulus_local hε.1 hε.2.le hRT hF
  apply tendsto_nhds_unique (integral_annulus_tendsto hi)
  simpa only [sub_zero] using (tendsto_const_nhds.sub hzero).congr' he.symm

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


def coneSpatialCoefficient (x y v e : Vec) : ℝ :=
  dot (coneDirection x y) e/(1-dot (coneDirection x y) (velocity v))

def coneSpatialLift (x y v e : Vec) : Vec :=
  e+coneSpatialCoefficient x y v e • velocity v

lemma coneSpatialCoefficient_identity {x y : Vec} (hxy : x≠y) (v e : Vec) :
    dot (coneDirection x y) (coneSpatialLift x y v e)=coneSpatialCoefficient x y v e := by
  have hd := (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne'
  simp only [coneSpatialLift,dot_add_right,dot_smul_right,coneSpatialCoefficient]
  field_simp
  ring

lemma retarded_spatial_division {f : Particle} {x y v K e : Vec} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t-coneRadius x y,y,v)) (hxy : x≠y)
    (heq : fderiv ℝ f (t-coneRadius x y,y,v) (1,velocity v,K)=0) :
    fderiv ℝ (fun z : Phase => f (t-coneRadius x z.1,z)) (y,v)
      (coneSpatialLift x y v e,coneSpatialCoefficient x y v e • K)=
    fderiv ℝ f (t-coneRadius x y,y,v) (0,e,0) := by
  rw [retarded_transport_chain hf hxy,coneSpatialCoefficient_identity hxy]
  have hv : (coneSpatialCoefficient x y v e,coneSpatialLift x y v e,
      coneSpatialCoefficient x y v e • K) =
      ((0:ℝ),e,(0:Vec))+coneSpatialCoefficient x y v e • ((1:ℝ),velocity v,K) := by
    ext <;> simp [coneSpatialLift]
  rw [hv,map_add,map_smul,heq,smul_zero,add_zero]

lemma phase_divergence_split {g : Phase → ℝ} {W V : Phase → Vec} {y v : Vec}
    (hg : DifferentiableAt ℝ g (y,v))
    (hW : DifferentiableAt ℝ W (y,v)) (hV : DifferentiableAt ℝ V (y,v)) :
    divergence (fun z => g (z,v) • W (z,v)) y+
      divergence (fun w => g (y,w) • V (y,w)) v =
      fderiv ℝ g (y,v) (W (y,v),V (y,v))+
      g (y,v)*(divergence (fun z => W (z,v)) y+divergence (fun w => V (y,w)) v) := by
  have hy : DifferentiableAt ℝ (fun z : Vec => (z,v)) y :=
    differentiableAt_id.prodMk (differentiableAt_const v)
  have hv : DifferentiableAt ℝ (fun w : Vec => (y,w)) v :=
    (differentiableAt_const y).prodMk differentiableAt_id
  have hgy : DifferentiableAt ℝ (fun z => g (z,v)) y := hg.comp y hy
  have hWy : DifferentiableAt ℝ (fun z => W (z,v)) y := hW.comp y hy
  have hgv : DifferentiableAt ℝ (fun w => g (y,w)) v := hg.comp v hv
  have hVv : DifferentiableAt ℝ (fun w => V (y,w)) v := hV.comp v hv
  rw [divergence_smul hgy hWy,
    divergence_smul hgv hVv,
    dot_gradient_direction,dot_gradient_direction]
  rw [←fderiv_phase_split hg]
  ring

lemma differentiableAt_coneSpatialCoefficient {x y v e : Vec} (hxy : x≠y) :
    DifferentiableAt ℝ (fun z : Phase => coneSpatialCoefficient x z.1 z.2 e) (y,v) := by
  have hn : DifferentiableAt ℝ (fun z : Phase => coneDirection x z.1) (y,v) :=
    (differentiableAt_coneDirection hxy).comp (f:=fun z : Phase => z.1) (y,v) differentiableAt_fst
  have hu : DifferentiableAt ℝ (fun z : Phase => velocity z.2) (y,v) :=
    (contDiff_velocity.differentiable (by simp : (∞:ℕ∞ω)≠0) v).comp
      (f:=fun z : Phase => z.2) (y,v) differentiableAt_snd
  have he : DifferentiableAt ℝ (fun z : Phase => dot (coneDirection x z.1) e) (y,v) := by
    simpa only [dot_eq_inner] using hn.inner ℝ (differentiableAt_const e)
  have hd : DifferentiableAt ℝ (fun z : Phase => 1-dot (coneDirection x z.1) (velocity z.2)) (y,v) := by
    exact (differentiableAt_const (1:ℝ)).sub (by simpa only [dot_eq_inner] using hn.inner ℝ hu)
  change DifferentiableAt ℝ (fun z : Phase => dot (coneDirection x z.1) e /
    (1-dot (coneDirection x z.1) (velocity z.2))) (y,v)
  convert he.mul (hd.inv (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne') using 1
  rfl

lemma retarded_spatial_divergence {f : Particle} {K : Phase → Vec} {k : Phase → ℝ}
    {x y v e : Vec} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t-coneRadius x y,y,v)) (hxy : x≠y)
    (hK : DifferentiableAt ℝ K (y,v)) (hk : DifferentiableAt ℝ k (y,v))
    (heq : fderiv ℝ f (t-coneRadius x y,y,v) (1,velocity v,K (y,v))=0) :
    k (y,v)*fderiv ℝ f (t-coneRadius x y,y,v) (0,e,0)=
      divergence (fun z => (f (t-coneRadius x z,z,v)*k (z,v)) • coneSpatialLift x z v e) y+
      divergence (fun w => (f (t-coneRadius x y,y,w)*k (y,w)) •
        (coneSpatialCoefficient x y w e • K (y,w))) v-
      f (t-coneRadius x y,y,v)*
        (divergence (fun z => k (z,v) • coneSpatialLift x z v e) y+
          divergence (fun w => k (y,w) • (coneSpatialCoefficient x y w e • K (y,w))) v) := by
  have hi : DifferentiableAt ℝ (fun z : Phase => (t-coneRadius x z.1,z)) (y,v) :=
    ((differentiableAt_const t).sub
      ((differentiableAt_coneRadius hxy).comp (f:=fun z : Phase => z.1) (y,v) differentiableAt_fst)).prodMk differentiableAt_id
  have hg : DifferentiableAt ℝ (fun z : Phase => f (t-coneRadius x z.1,z)) (y,v) :=
    hf.comp (f:=fun z : Phase => (t-coneRadius x z.1,z)) (y,v) hi
  have hc := differentiableAt_coneSpatialCoefficient (v:=v) (e:=e) hxy
  have hu : DifferentiableAt ℝ (fun z : Phase => velocity z.2) (y,v) :=
    (contDiff_velocity.differentiable (by simp : (∞:ℕ∞ω)≠0) v).comp
      (f:=fun z : Phase => z.2) (y,v) differentiableAt_snd
  have hW : DifferentiableAt ℝ (fun z : Phase => k z • coneSpatialLift x z.1 z.2 e) (y,v) :=
    hk.smul ((differentiableAt_const e).add (hc.smul hu))
  have hV : DifferentiableAt ℝ (fun z : Phase => k z •
      (coneSpatialCoefficient x z.1 z.2 e • K z)) (y,v) := hk.smul (hc.smul hK)
  have hh := phase_divergence_split hg hW hV
  dsimp only at hh
  have hp : (k (y,v) • coneSpatialLift x y v e,
      k (y,v) • (coneSpatialCoefficient x y v e • K (y,v))) =
      k (y,v) • (coneSpatialLift x y v e,coneSpatialCoefficient x y v e • K (y,v)) := rfl
  rw [hp,map_smul,retarded_spatial_division hf hxy heq] at hh
  simp only [smul_eq_mul] at hh
  simpa only [←smul_smul,smul_eq_mul] using (eq_sub_iff_add_eq.mpr hh.symm)

end RVM

end

end OAI
