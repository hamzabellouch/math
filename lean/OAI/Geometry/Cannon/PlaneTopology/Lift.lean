import Mathlib

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

namespace CannonWinding

def lift (f : C(I,Circle)) : C(I,ℝ) :=
  Circle.isCoveringMap_exp.liftPath f (Complex.arg (f 0)) (Circle.exp_arg (f 0)).symm

lemma lift_exp (f : C(I,Circle)) (t : I) : Circle.exp (lift f t)=f t :=
  congr_fun (Circle.isCoveringMap_exp.liftPath_lifts f _ _) t

def turn (f : C(I,Circle)) : ℝ := lift f 1-lift f 0

lemma turn_eq_of_lift (f : C(I,Circle)) (g : C(I,ℝ))
    (hg : ∀ t, Circle.exp (g t)=f t) : turn f=g 1-g 0 := by
  have hconst : ∀ t t', g t-lift f t=g t'-lift f t' := by
    apply Circle.isCoveringMap_exp.const_of_comp (g.continuous.sub (lift f).continuous)
    intro t t'
    change Circle.exp (g t-lift f t)=Circle.exp (g t'-lift f t')
    simp only [Circle.exp_sub,hg,lift_exp,div_self']
  have h := hconst 1 0
  dsimp only [turn]
  linarith

lemma turn_const (z : Circle) : turn (.const I z)=0 := by
  rw [turn_eq_of_lift (.const I z) (.const I (Complex.arg z)) (fun _ => Circle.exp_arg z)]
  simp

lemma turn_homotopy (H : C(I×I,Circle)) (hH : ∀ s, H (s,0)=H (s,1)) :
    turn (H.comp ⟨fun t => (0,t),by fun_prop⟩)=
      turn (H.comp ⟨fun t => (1,t),by fun_prop⟩) := by
  let f := H.comp (⟨fun t => (0,t),by fun_prop⟩ : C(I,I×I))
  let g := lift f
  have h₀ (t : I) : H (0,t)=Circle.exp (g t) := (lift_exp f t).symm
  let L := Circle.isCoveringMap_exp.liftHomotopy H g h₀
  have hL (s t : I) : Circle.exp (L (s,t))=H (s,t) :=
    congr_fun (Circle.isCoveringMap_exp.liftHomotopy_lifts H g h₀) (s,t)
  have heq : ∀ s s', L (s,1)-L (s,0)=L (s',1)-L (s',0) := by
    apply Circle.isCoveringMap_exp.const_of_comp (by fun_prop)
    intro s s'
    simp only [Circle.exp_sub,hL,←hH,div_self']
  rw [turn_eq_of_lift (H.comp ⟨fun t => (0,t),by fun_prop⟩) (L.comp ⟨fun t => (0,t),by fun_prop⟩) (fun t => hL 0 t),
    turn_eq_of_lift (H.comp ⟨fun t => (1,t),by fun_prop⟩) (L.comp ⟨fun t => (1,t),by fun_prop⟩) (fun t => hL 1 t)]
  exact heq 0 1

lemma turn_integer (f : C(I,Circle)) (hf : f 0=f 1) :
    ∃ n : ℤ, turn f=n*(2*Real.pi) := by
  apply Circle.exp_eq_one.mp
  simp only [turn,Circle.exp_sub,lift_exp,←hf,div_self']

lemma turn_standard_loop :
    turn (Circle.exp.comp ⟨fun t : I => 2*Real.pi*(t:ℝ),by fun_prop⟩)=2*Real.pi := by
  rw [turn_eq_of_lift _ ⟨fun t : I => 2*Real.pi*(t:ℝ),by fun_prop⟩ (fun _ => rfl)]
  simp

end CannonWinding

namespace CannonWinding
variable {A : Type*} [TopologicalSpace A]

def direction (f : C(A,ℂ)) (hf : ∀ x, f x≠0) : C(A,Circle) := by
  let v (x : A) : Circle := ⟨f x/(‖f x‖:ℂ),by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr (hf x))]⟩
  refine ⟨v,?_⟩
  apply Continuous.subtype_mk
  exact f.continuous.div (Complex.continuous_ofReal.comp f.continuous.norm)
    (fun x => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hf x)))

@[simp] lemma direction_coe (f : C(A,ℂ)) (hf : ∀ x, f x≠0) (x : A) :
    (direction f hf x:ℂ)=f x/(‖f x‖:ℂ) := rfl

lemma direction_congr (f g : C(A,ℂ)) (hf : ∀ x, f x≠0) (hg : ∀ x, g x≠0)
    (heq : ∀ x, f x=g x) : direction f hf=direction g hg := by
  ext x
  simp only [direction_coe,heq]

def winding (f : C(I,ℂ)) (z : ℂ) (hz : z∉range f) : ℝ :=
  turn (direction (f-.const I z) (fun t ht => hz ⟨t,sub_eq_zero.mp ht⟩))

lemma winding_homotopy (H : C(I×I,ℂ)) (hclosed : ∀ s, H (s,0)=H (s,1))
    (z : ℂ) (hz : z∉range H) :
    winding (H.comp ⟨fun t => (0,t),by fun_prop⟩) z
      (fun h => hz <| by rcases h with ⟨t,ht⟩; exact ⟨(0,t),ht⟩)=
    winding (H.comp ⟨fun t => (1,t),by fun_prop⟩) z
      (fun h => hz <| by rcases h with ⟨t,ht⟩; exact ⟨(1,t),ht⟩) := by
  let K := direction (H-.const (I×I) z) (fun p hp => hz ⟨p,sub_eq_zero.mp hp⟩)
  have hc (s : I) : K (s,0)=K (s,1) := by
    apply Circle.ext
    simp only [K,direction_coe,ContinuousMap.sub_apply,ContinuousMap.const_apply,hclosed]
  exact turn_homotopy K hc

lemma winding_moving_point (f : C(I,ℂ)) (hf : f 0=f 1) (p : C(I,ℂ))
    (hp : ∀ s, p s∉range f) : winding f (p 0) (hp 0)=winding f (p 1) (hp 1) := by
  let H : C(I×I,ℂ) := ⟨fun z => f z.2-p z.1,by fun_prop⟩
  have hH (z : I×I) : H z≠0 := fun h => hp z.1 ⟨z.2,sub_eq_zero.mp h⟩
  let K := direction H hH
  have hc (s : I) : K (s,0)=K (s,1) := by
    apply Circle.ext
    simp only [K,direction_coe,H,ContinuousMap.coe_mk,hf]
  exact turn_homotopy K hc

lemma winding_const (a z : ℂ) (hz : z∉range (ContinuousMap.const I a)) :
    winding (.const I a) z hz=0 := by
  let k := direction (ContinuousMap.const I a-.const I z)
    (fun t ht => hz ⟨t,sub_eq_zero.mp ht⟩)
  change turn k=0
  have hk : k=.const I (k 0) := by ext t; rfl
  rw [hk,turn_const]

end CannonWinding

namespace CannonWinding
open Metric

lemma winding_eq_of_homotopy (f g : C(I,ℂ)) (z : ℂ) (hf : z∉range f) (hg : z∉range g)
    (H : C(I×I,ℂ)) (hclosed : ∀ s, H (s,0)=H (s,1))
    (h₀ : ∀ t, H (0,t)=f t) (h₁ : ∀ t, H (1,t)=g t) (hz : z∉range H) :
    winding f z hf=winding g z hg := by
  have h₀' : H.comp ⟨fun t => (0,t),by fun_prop⟩=f := ContinuousMap.ext h₀
  have h₁' : H.comp ⟨fun t => (1,t),by fun_prop⟩=g := ContinuousMap.ext h₁
  simpa only [h₀',h₁'] using winding_homotopy H hclosed z hz

theorem winding_locally_constant (f : C(I,ℂ)) (hf : f 0=f 1) :
    IsLocallyConstant (fun z : ↥((range f)ᶜ) => winding f z.val z.property) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro z
  have ho : IsOpen ((range f)ᶜ) := (isCompact_range f.continuous).isClosed.isOpen_compl
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds z.property)
  refine ⟨Subtype.val ⁻¹' ball z.val ε,isOpen_ball.preimage continuous_subtype_val,
    mem_ball_self hε,?_⟩
  intro w hw
  have hp (s : I) : Path.segment z.val w.val s∉range f := by
    apply hball
    apply (convex_ball z.val ε).segment_subset (mem_ball_self hε) hw
    rw [←Path.range_segment]
    exact mem_range_self s
  have heq := winding_moving_point f hf (Path.segment z.val w.val).toContinuousMap hp
  change winding f (Path.segment z.val w.val 0) _ =
    winding f (Path.segment z.val w.val 1) _ at heq
  simpa only [Path.source,Path.target] using heq.symm

lemma winding_convex_zero (f : C(I,ℂ)) (hf : f 0=f 1) {S : Set ℂ}
    (hS : Convex ℝ S) (hfrange : range f⊆S) {z : ℂ} (hzS : z∉S) :
    winding f z (fun hz => hzS (hfrange hz))=0 := by
  let a := f 0
  let H : C(I×I,ℂ) := ⟨fun w => (1-(w.1:ℝ)) • f w.2+(w.1:ℝ) • a,by fun_prop⟩
  have hH (w : I×I) : H w∈S := by
    exact hS (hfrange (mem_range_self w.2)) (hfrange (mem_range_self 0))
      (sub_nonneg.mpr w.1.property.2) w.1.property.1 (by ring)
  have hclosed (s : I) : H (s,0)=H (s,1) := by simp only [H,ContinuousMap.coe_mk,hf]
  have h₀ (t : I) : H (0,t)=f t := by simp [H]
  have h₁ (t : I) : H (1,t)=a := by simp [H]
  have hz : z∉range H := by rintro ⟨w,rfl⟩; exact hzS (hH w)
  have hza : z∉range (ContinuousMap.const I a) := by
    rintro ⟨t,ht⟩
    exact hzS (ht ▸ hfrange (mem_range_self 0))
  rw [winding_eq_of_homotopy f (.const I a) z _ hza H hclosed h₀ h₁ hz]
  exact winding_const a z hza

def roundLoop (a : ℂ) (R : ℝ) : C(I,ℂ) :=
  ⟨fun t => a+(R:ℂ)*(Circle.exp (2*Real.pi*(t:ℝ)):ℂ),by fun_prop⟩

lemma roundLoop_closed (a : ℂ) (R : ℝ) : roundLoop a R 0=roundLoop a R 1 := by
  simp [roundLoop]

lemma roundLoop_dist (a : ℂ) {R : ℝ} (hR : 0≤R) (t : I) : dist (roundLoop a R t) a=R := by
  simp only [dist_eq_norm,roundLoop,ContinuousMap.coe_mk,add_sub_cancel_left,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR,Circle.norm_coe,mul_one]

lemma center_not_roundLoop (a : ℂ) {R : ℝ} (hR : 0<R) : a∉range (roundLoop a R) := by
  rintro ⟨t,ht⟩
  have h := roundLoop_dist a hR.le t
  rw [ht,dist_self] at h
  exact hR.ne' h.symm

lemma winding_roundLoop_center (a : ℂ) {R : ℝ} (hR : 0<R) :
    winding (roundLoop a R) a (center_not_roundLoop a hR)=2*Real.pi := by
  have heq : direction (roundLoop a R-.const I a)
      (fun t ht => center_not_roundLoop a hR ⟨t,sub_eq_zero.mp ht⟩)=
      Circle.exp.comp ⟨fun t : I => 2*Real.pi*(t:ℝ),by fun_prop⟩ := by
    ext t
    simp only [direction_coe,ContinuousMap.sub_apply,ContinuousMap.const_apply,
      roundLoop,ContinuousMap.coe_mk,add_sub_cancel_left,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR,Circle.norm_coe,mul_one,
      ContinuousMap.comp_apply]
    field_simp [Complex.ofReal_ne_zero.mpr hR.ne']
  simp only [winding,heq,turn_standard_loop]

lemma winding_roundLoop_inside (a z : ℂ) {R : ℝ} (hR : 0<R) (hz : dist z a<R) :
    ∃ h : z∉range (roundLoop a R), winding (roundLoop a R) z h=2*Real.pi := by
  have hp (s : I) : Path.segment a z s∉range (roundLoop a R) := by
    have hs : Path.segment a z s∈ball a R := by
      apply (convex_ball a R).segment_subset (mem_ball_self hR) hz
      rw [←Path.range_segment]; exact mem_range_self s
    rintro ⟨t,ht⟩
    have hd := roundLoop_dist a hR.le t
    rw [ht] at hd
    exact hs.not_ge hd.ge
  have hz' : z∉range (roundLoop a R) := by simpa only [Path.target] using hp 1
  refine ⟨hz',?_⟩
  have heq := winding_moving_point (roundLoop a R) (roundLoop_closed a R)
    (Path.segment a z).toContinuousMap hp
  change winding (roundLoop a R) (Path.segment a z 0) _ =
    winding (roundLoop a R) (Path.segment a z 1) _ at heq
  have heq' : winding (roundLoop a R) a (center_not_roundLoop a hR)=
      winding (roundLoop a R) z hz' := by simpa only [Path.source,Path.target] using heq
  rw [←heq',winding_roundLoop_center a hR]

end CannonWinding

namespace CannonWinding
open Metric

lemma winding_stable_near (f g : C(I,ℂ)) (hf : f 0=f 1) (hg : g 0=g 1)
    (z : ℂ) (hz : z∉range f) (hnear : ∀ t, dist (g t) (f t)<dist (f t) z) :
    ∃ hg' : z∉range g, winding f z hz=winding g z hg' := by
  let H : C(I×I,ℂ) := ⟨fun w => (1-(w.1:ℝ)) • f w.2+(w.1:ℝ) • g w.2,by fun_prop⟩
  have hdist (s t : I) : dist (H (s,t)) (f t)≤dist (g t) (f t) := by
    have heq : H (s,t)-f t=(s:ℝ) • (g t-f t) := by
      dsimp only [H,ContinuousMap.coe_mk]
      module
    rw [dist_eq_norm,heq,norm_smul,Real.norm_eq_abs,abs_of_nonneg s.property.1]
    rw [dist_eq_norm]
    exact mul_le_of_le_one_left (norm_nonneg (g t-f t)) s.property.2
  have hH : z∉range H := by
    rintro ⟨⟨s,t⟩,heq⟩
    have h := (hdist s t).trans_lt (hnear t)
    rw [heq,dist_comm z (f t)] at h
    exact h.false
  have h₀ (t : I) : H (0,t)=f t := by simp [H]
  have h₁ (t : I) : H (1,t)=g t := by simp [H]
  have hg' : z∉range g := by
    rintro ⟨t,ht⟩
    exact hH ⟨(1,t),(h₁ t).trans ht⟩
  refine ⟨hg',winding_eq_of_homotopy f g z hz hg' H ?_ h₀ h₁ hH⟩
  intro s
  simp only [H,ContinuousMap.coe_mk,hf,hg]

def index (f : C(I,ℂ)) (z : ℂ) : ℝ := by
  classical
  exact if hz : z∉range f then winding f z hz else 0

lemma index_eq (f : C(I,ℂ)) {z : ℂ} (hz : z∉range f) : index f z=winding f z hz := by
  simp only [index,dite_eq_left hz]

lemma index_eventually_eq (f : C(I,ℂ)) (hf : f 0=f 1) {z : ℂ} (hz : z∉range f) :
    ∀ᶠ w in 𝓝 z, index f w=index f z := by
  have ho : IsOpen ((range f)ᶜ) := (isCompact_range f.continuous).isClosed.isOpen_compl
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hz)
  filter_upwards [Metric.ball_mem_nhds z hε] with w hw
  have hw' : w∉range f := hball hw
  rw [index_eq f hw',index_eq f hz]
  have hp (s : I) : Path.segment z w s∉range f := by
    apply hball
    apply (convex_ball z ε).segment_subset (mem_ball_self hε) hw
    rw [←Path.range_segment]; exact mem_range_self s
  have heq := winding_moving_point f hf (Path.segment z w).toContinuousMap hp
  change winding f (Path.segment z w 0) _ = winding f (Path.segment z w 1) _ at heq
  simpa only [Path.source,Path.target] using heq.symm

lemma index_zero_outside_closedBall (f : C(I,ℂ)) (hf : f 0=f 1)
    (a : ℂ) (R : ℝ) (hbound : ∀ t, dist (f t) a≤R) {z : ℂ} (hz : R<dist z a) :
    index f z=0 := by
  have hfr : range f⊆closedBall a R := by rintro _ ⟨t,rfl⟩; exact hbound t
  have hzS : z∉closedBall a R := not_le.mpr hz
  have hz' : z∉range f := fun h => hzS (hfr h)
  rw [index_eq f hz']
  exact winding_convex_zero f hf (convex_closedBall a R) hfr hzS

lemma index_near_roundLoop (a : ℂ) {R : ℝ} (hR : 0<R) (g : C(I,ℂ))
    (hg : g 0=g 1) (hnear : ∀ t, dist (g t) (roundLoop a (R/2) t)<R/4)
    {z : ℂ} (hz : dist z a<R/4) : index g z=2*Real.pi := by
  obtain ⟨hzf,hwind⟩ := winding_roundLoop_inside a z (half_pos hR) (by linarith)
  have hclose (t : I) : dist (g t) (roundLoop a (R/2) t)<dist (roundLoop a (R/2) t) z := by
    have htri := dist_triangle (roundLoop a (R/2) t) z a
    rw [roundLoop_dist a (half_pos hR).le] at htri
    linarith [hnear t]
  obtain ⟨hzg,heq⟩ := winding_stable_near (roundLoop a (R/2)) g
    (roundLoop_closed a (R/2)) hg z hzf hclose
  rw [index_eq g hzg,←heq,hwind]

end CannonWinding

namespace CannonWinding
open Metric

variable {X : Type*} [TopologicalSpace X] [T2Space X]

def chartIndex (e : ℂ → X) (he : IsOpenEmbedding e) (f : C(I,ℂ)) (x : X) : ℝ := by
  classical
  exact if x∈range e then index f ((he.toOpenPartialHomeomorph e).symm x) else 0

omit [T2Space X] in
lemma chartIndex_apply (e : ℂ → X) (he : IsOpenEmbedding e) (f : C(I,ℂ)) (z : ℂ) :
    chartIndex e he f (e z)=index f z := by
  simp only [chartIndex,ite_eq_left (mem_range_self z),he.toOpenPartialHomeomorph_left_inv]

omit [T2Space X] in
lemma chartIndex_zero_off_disk (e : ℂ → X) (he : IsOpenEmbedding e)
    (f : C(I,ℂ)) (hf : f 0=f 1) (a : ℂ) (R : ℝ)
    (hbound : ∀ t, dist (f t) a≤R) {x : X} (hx : x∉e '' closedBall a R) :
    chartIndex e he f x=0 := by
  classical
  by_cases hxe : x∈range e
  · obtain ⟨z,rfl⟩ := hxe
    rw [chartIndex_apply]
    apply index_zero_outside_closedBall f hf a R hbound
    apply lt_of_not_ge
    intro hz
    exact hx ⟨z,hz,rfl⟩
  · simp only [chartIndex,ite_eq_right hxe]

lemma chartIndex_eventually_eq (e : ℂ → X) (he : IsOpenEmbedding e)
    (f : C(I,ℂ)) (hf : f 0=f 1) (a : ℂ) (R : ℝ)
    (hbound : ∀ t, dist (f t) a≤R) {x : X} (hx : x∉range (e ∘ f)) :
    ∀ᶠ y in 𝓝 x, chartIndex e he f y=chartIndex e he f x := by
  classical
  by_cases hxe : x∈range e
  · let h := he.toOpenPartialHomeomorph e
    have hinv : e (h.symm x)=x := he.toOpenPartialHomeomorph_right_inv e hxe
    have hz : h.symm x∉range f := by
      rintro ⟨t,ht⟩
      exact hx ⟨t,by change e (f t)=x; rw [ht,hinv]⟩
    have hc : ContinuousAt h.symm x := h.symm.continuousAt (by
      simpa only [OpenPartialHomeomorph.symm_source,h,IsOpenEmbedding.toOpenPartialHomeomorph_target] using hxe)
    have hv := hc.eventually (index_eventually_eq f hf hz)
    filter_upwards [hv,he.isOpen_range.mem_nhds hxe] with y hy hye
    simpa only [chartIndex,ite_eq_left hye,ite_eq_left hxe] using hy
  · have hxK : x∉e '' closedBall a R := fun hk => hxe (image_subset_range _ _ hk)
    have hc : IsClosed (e '' closedBall a R) :=
      ((isCompact_closedBall a R).image he.continuous).isClosed
    filter_upwards [hc.isOpen_compl.mem_nhds hxK] with y hy
    rw [chartIndex_zero_off_disk e he f hf a R hbound hy,
      chartIndex_zero_off_disk e he f hf a R hbound hxK]

theorem chartIndex_eq_on_preconnected (e : ℂ → X) (he : IsOpenEmbedding e)
    (f : C(I,ℂ)) (hf : f 0=f 1) (a : ℂ) (R : ℝ)
    (hbound : ∀ t, dist (f t) a≤R) {S : Set X} (hS : IsPreconnected S)
    (havoid : S⊆(range (e ∘ f))ᶜ) {x y : X} (hx : x∈S) (hy : y∈S) :
    chartIndex e he f x=chartIndex e he f y := by
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  have hc : IsLocallyConstant (fun z : S => chartIndex e he f z.val) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    exact continuous_subtype_val.continuousAt.eventually
      (chartIndex_eventually_eq e he f hf a R hbound (havoid z.property))
  exact hc.apply_eq_of_preconnectedSpace ⟨x,hx⟩ ⟨y,hy⟩

theorem near_roundLoop_separates (e : ℂ → X) (he : IsOpenEmbedding e)
    (a : ℂ) {R : ℝ} (hR : 0<R) (g : C(I,ℂ)) (hg : g 0=g 1)
    (hnear : ∀ t, dist (g t) (roundLoop a (R/2) t)<R/4)
    {S : Set X} (hS : IsPreconnected S) (havoid : S⊆(range (e ∘ g))ᶜ)
    {z : ℂ} (hz : dist z a<R/4) (hzS : e z∈S) : S⊆e '' closedBall a R := by
  have hbound (t : I) : dist (g t) a≤R := by
    have h := dist_triangle (g t) (roundLoop a (R/2) t) a
    rw [roundLoop_dist a (half_pos hR).le] at h
    linarith [hnear t]
  intro y hy
  by_contra hyK
  have heq := chartIndex_eq_on_preconnected e he g hg a R hbound hS havoid hzS hy
  rw [chartIndex_apply,index_near_roundLoop a hR g hg hnear hz,
    chartIndex_zero_off_disk e he g hg a R hbound hyK] at heq
  have := Real.pi_pos
  linarith

end CannonWinding

namespace CannonWinding
open Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X]

lemma chart_loop_neighborhood (e : ℂ → X) (he : IsOpenEmbedding e)
    (f : C(I,ℂ)) {d : ℝ} (hd : 0<d) :
    ∃ ε : ℝ, 0<ε ∧ ∀ t : I, ∀ y : X, dist y (e (f t))<ε →
      y∈range e ∧ dist ((he.toOpenPartialHomeomorph e).symm y) (f t)<d := by
  let K : Set X := range (e ∘ f)
  have hK : IsCompact K := isCompact_range (he.continuous.comp f.continuous)
  obtain ⟨δ,hδ,hδsub⟩ := hK.exists_cthickening_subset_open he.isOpen_range
    (by rintro _ ⟨t,rfl⟩; exact mem_range_self _)
  let U : Set X := cthickening δ K
  let h := he.toOpenPartialHomeomorph e
  have hc : ContinuousOn h.symm U := by
    apply h.symm.continuousOn.mono
    simpa only [h,OpenPartialHomeomorph.symm_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target] using hδsub
  have hu : UniformContinuousOn h.symm U := (isClosed_cthickening (δ:=δ) (E:=K)).isCompact.uniformContinuousOn_of_continuous hc
  obtain ⟨ε,hε,hεeq⟩ := Metric.uniformContinuousOn_iff.mp hu d hd
  refine ⟨min δ ε,lt_min hδ hε,fun t y hy => ?_⟩
  have ht : e (f t)∈K := mem_range_self t
  have hyU : y∈U := closedBall_subset_cthickening ht δ ((hy.trans_le (min_le_left ..)).le)
  have htU : e (f t)∈U := self_subset_cthickening K ht
  refine ⟨hδsub hyU,?_⟩
  have hh := hεeq y hyU (e (f t)) htU (hy.trans_le (min_le_right ..))
  simpa only [h,he.toOpenPartialHomeomorph_left_inv] using hh

def complexPlane : ℂ ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  Complex.equivRealProdCLM.toHomeomorph.trans
    (Homeomorph.finTwoArrow.symm.trans (EuclideanSpace.equiv (𝕜:=ℝ) (ι:=Fin 2)).toHomeomorph.symm)

omit [CompactSpace X] in
lemma small_complex_chart (φ : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (x : X) {η : ℝ} (hη : 0<η) :
    ∃ (e : ℂ → X), IsOpenEmbedding e ∧ ∃ (a : ℂ) (R : ℝ),
      e a=x ∧ 0<R ∧ e '' closedBall a R⊆ball x η := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2+1) := ⟨by simp⟩
  let h := stereographic' 2 (-φ x)
  have ht : h.target=univ := stereographic'_target _
  have hx : φ x∈h.source := by
    rw [show h.source={-φ x}ᶜ from stereographic'_source _]
    exact ne_neg_of_mem_unit_sphere ℝ (φ x)
  let e : ℂ → X := φ.symm ∘ h.symm ∘ complexPlane
  have he : IsOpenEmbedding e :=
    φ.symm.isOpenEmbedding.comp ((h.symm.isOpenEmbedding ht).comp complexPlane.isOpenEmbedding)
  let a := complexPlane.symm (h (φ x))
  have hea : e a=x := by
    dsimp only [e,a,Function.comp_apply]
    rw [complexPlane.apply_symm_apply,h.left_inv hx,φ.symm_apply_apply]
  have hn : e ⁻¹' ball x η∈𝓝 a := by
    apply he.continuous.continuousAt.preimage_mem_nhds
    rw [hea]
    exact ball_mem_nhds x hη
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨e,he,a,r/2,hea,half_pos hr,?_⟩
  rintro _ ⟨z,hz,rfl⟩
  exact hs (hz.trans_lt (half_lt_self hr))

theorem uniform_robust_separating_loops
    (φ : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {η : ℝ} (hη : 0<η) :
    ∃ ε : ℝ, 0<ε ∧ ∀ x : X, ∃ f : C(I,X), f 0=f 1 ∧
      ∀ g : C(I,X), g 0=g 1 → (∀ t, dist (g t) (f t)<ε) →
      ∀ S : Set X, IsPreconnected S → S⊆(range g)ᶜ → x∈S → S⊆ball x η := by
  classical
  choose e he a R hea hR hsmall using fun p : X => small_complex_chart φ p (half_pos hη)
  let U (p : X) := e p '' ball (a p) (R p/4)
  have hU (p : X) : IsOpen (U p) := (he p).isOpenMap _ isOpen_ball
  have hpU (p : X) : p∈U p := ⟨a p,mem_ball_self (div_pos (hR p) (by norm_num)),hea p⟩
  have hcover : (univ : Set X)⊆⋃ p, U p := fun x _ => mem_iUnion.mpr ⟨x,hpU x⟩
  obtain ⟨T,hT⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  choose ε hε htolerance using fun p : X =>
    chart_loop_neighborhood (e p) (he p) (roundLoop (a p) (R p/2)) (show 0<R p/4 from div_pos (hR p) (by norm_num))
  obtain ⟨ε₀,hε₀,hε₀T⟩ : ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ p∈T, ε₀≤ε p := by
    clear hT
    induction T using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert p T hp ih =>
      obtain ⟨b,hb,hbT⟩ := ih
      refine ⟨min (ε p) b,lt_min (hε p) hb,?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl|hq
      · exact min_le_left ..
      · exact (min_le_right ..).trans (hbT q hq)
  refine ⟨ε₀,hε₀,fun x => ?_⟩
  obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (hT (mem_univ x))
  obtain ⟨z,hz,hzx⟩ := hx
  let f : C(I,X) := ⟨fun t => e p (roundLoop (a p) (R p/2) t),
    (he p).continuous.comp (roundLoop (a p) (R p/2)).continuous⟩
  refine ⟨f,by change e p _=e p _; rw [roundLoop_closed],fun g hg hnear S hS havoid hxS => ?_⟩
  have htol (t : I) := htolerance p t (g t) ((hnear t).trans_le (hε₀T p hp))
  let h := (he p).toOpenPartialHomeomorph (e p)
  let g' : C(I,ℂ) := ⟨fun t => h.symm (g t),by
    apply h.symm.continuousOn.comp_continuous g.continuous
    intro t
    simpa only [h,OpenPartialHomeomorph.symm_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target] using (htol t).1⟩
  have hg' : g' 0=g' 1 := by change h.symm (g 0)=h.symm (g 1); rw [hg]
  have hgg (t : I) : e p (g' t)=g t := (he p).toOpenPartialHomeomorph_right_inv _ (htol t).1
  have hbound := near_roundLoop_separates (e p) (he p) (a p) (hR p) g' hg'
    (fun t => (htol t).2) hS (show S⊆(range (e p ∘ g'))ᶜ by
      intro y hy hy'
      obtain ⟨t,ht⟩ := hy'
      exact havoid hy ⟨t,(hgg t).symm.trans ht⟩) hz (hzx.symm ▸ hxS)
  intro y hy
  have hyp := hsmall p (hbound hy)
  have hxp := hsmall p ⟨z,(hz.le.trans (show R p/4≤R p by linarith [hR p])),hzx⟩
  have htri := dist_triangle y p x
  rw [dist_comm p x] at htri
  change dist y p<η/2 at hyp
  change dist x p<η/2 at hxp
  change dist y x<η
  linarith

end CannonWinding

namespace CannonWinding
open Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem loop_approximation_separates
    (φ : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {C B η : ℝ} (hC : 0<C) (hB : 0<B) (hη : 0<η)
    (hexpand : ∀ x : X, ∀ s : ℝ, 0<s → s≤1 → ∃ f : X ≃ₜ X,
      (∀ y z, dist (f y) (f z)*s≤C*dist y z) ∧
      (∀ y, s≤dist x y → η≤dist (f x) (f y))) :
    ∃ L : ℝ, 1≤L ∧ ∀ r : ℝ, 0<r → r≤1/L → ∀ Q : Set X,
      (∀ f : C(I,X), f 0=f 1 → ∃ g : C(I,X), g 0=g 1 ∧ range g⊆Q ∧
        ∀ t, dist (g t) (f t)<B*r) →
      ∀ S : Set X, IsPreconnected S → S⊆Qᶜ → ∀ x∈S, ∀ y∈S, dist x y<L*r := by
  obtain ⟨ε,hε,htemplate⟩ := uniform_robust_separating_loops φ hη
  let L := 1+C*B/ε
  have hL : 1≤L := by dsimp [L]; linarith [div_pos (mul_pos hC hB) hε]
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hεL : C*B<ε*L := by
    dsimp [L]
    have heq : ε*(1+C*B/ε)=ε+C*B := by field_simp
    rw [heq]
    linarith
  refine ⟨L,hL,fun r hr hrs Q happrox S hS havoid x hx y hy => ?_⟩
  have hs : 0<L*r := mul_pos hLp hr
  have hs₁ : L*r≤1 := by
    have hh := (le_div_iff₀ hLp).mp hrs
    nlinarith
  obtain ⟨f,hfLip,hfFar⟩ := hexpand x (L*r) hs hs₁
  obtain ⟨l,hl,hsep⟩ := htemplate (f x)
  let l₀ : C(I,X) := ⟨fun t => f.symm (l t),by fun_prop⟩
  have hl₀ : l₀ 0=l₀ 1 := by change f.symm (l 0)=f.symm (l 1); rw [hl]
  obtain ⟨g,hg,hgQ,hgclose⟩ := happrox l₀ hl₀
  let g₁ : C(I,X) := ⟨fun t => f (g t),by fun_prop⟩
  have hg₁ : g₁ 0=g₁ 1 := by change f (g 0)=f (g 1); rw [hg]
  have hclose (t : I) : dist (g₁ t) (l t)<ε := by
    have hh := hfLip (g t) (l₀ t)
    have ht : f (l₀ t)=l t := f.apply_symm_apply _
    rw [ht] at hh
    have hgt := mul_lt_mul_of_pos_left (hgclose t) hC
    have hq : dist (g₁ t) (l t)*L<C*B := by
      change dist (f (g t)) (l t)*L<C*B
      nlinarith [hh,hgt]
    nlinarith [hq,hεL]
  have hSf : IsPreconnected (f '' S) := hS.image f f.continuous.continuousOn
  have hSfavoid : f '' S⊆(range g₁)ᶜ := by
    rintro _ ⟨z,hz,rfl⟩ ⟨t,ht⟩
    have htz : g t=z := f.injective ht
    exact havoid hz (htz ▸ hgQ (mem_range_self t))
  have hsmall := hsep g₁ hg₁ hclose (f '' S) hSf hSfavoid (mem_image_of_mem f hx)
  have hyclose := hsmall (mem_image_of_mem f hy)
  change dist (f y) (f x)<η at hyclose
  rw [dist_comm] at hyclose
  by_contra hxy
  exact (hfFar y (le_of_not_gt hxy)).not_gt hyclose

end CannonWinding

end
end
end
end
end
end
end

end OAI
