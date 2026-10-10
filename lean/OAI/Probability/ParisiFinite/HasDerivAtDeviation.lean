import Mathlib
import OAI.Probability.ParisiFinite.Mix

namespace OAI

/-! Has Deriv At Deviation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
namespace ParisiFinite
open ParisiPath BoundedCoefficient
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
variable {β : ℝ≥0}

lemma hasDerivAt_deviation (hW : IsBrownianReal W P) (hβ : 0<β)
    (c : BoundedCoefficient β) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (deviation P W hβ c) (c.expectedSquareCurvature P W hβ t-1) t :=
  (hasDerivAt_expectedProduct_self hW hβ c t ht).sub (hasDerivAt_id t)

 

theorem minimizingParisi_replicon (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {t : OrderPoint} (ht : t∈(ρ:Measure OrderPoint).support)
    (h0 : 0<(t:ℝ)) (h1 : (t:ℝ)<1) :
    (ofMeasure β ρ).expectedSquareCurvature P W hβ t≤1 := by
  by_contra hn
  have hp : 0<(ofMeasure β ρ).expectedSquareCurvature P W hβ t-1 := sub_pos.mpr (not_le.mp hn)
  let c := ofMeasure β ρ
  let g := deviation P W hβ c
  have hg : Continuous g := continuous_deviation hW hβ c
  have ht0 : g t=0 := minimizingParisi_deviation_interior hW hβ hρ ht h0 h1
  have hs := ((hasDerivAt_deviation hW hβ c t ⟨h0,h1⟩).tendsto_slope.mono_left
    (nhdsGT_le_nhdsNE (t:ℝ))).eventually (lt_mem_nhds hp)
  have hev : ∀ᶠ s in 𝓝[>] (t:ℝ),0<g s ∧ s<1 := by
    filter_upwards [hs,self_mem_nhdsWithin,
      (eventually_lt_nhds h1).filter_mono nhdsWithin_le_nhds] with s hs hst hs1
    refine ⟨?_,hs1⟩
    rw [slope_def_field] at hs
    change 0<(g s-g t)/(s-(t:ℝ)) at hs
    rw [ht0,sub_zero] at hs
    exact (div_pos_iff_of_pos_right (sub_pos.mpr hst)).mp hs
  obtain ⟨u,hu,hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  have hu1 : u<1 := (hsub ⟨hu,le_rfl⟩).2
  have hi : 0<∫ s in (t:ℝ)..u,g s :=
    intervalIntegral.integral_pos hu hg.continuousOn
      (fun s hs => (hsub hs).1.le) ⟨u,⟨hu.le,le_rfl⟩,(hsub ⟨hu,le_rfl⟩).1⟩
  have hmin := minimizingParisi_support_potential hW hβ hρ ht
    ⟨u,(h0.trans hu).le,hu1.le⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) (t:ℝ) u) (hg.intervalIntegrable (μ := volume) u 1)
  change (∫ s in (t:ℝ)..1,g s)≤∫ s in u..1,g s at hmin
  linarith

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
namespace ParisiFinite
open ParisiPath BoundedCoefficient
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
variable {β : ℝ≥0}

theorem minimizingParisi_support_endpoint (hW : IsBrownianReal W P) (hβ : (1:ℝ)<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ) :
    ∃ q : OrderPoint, 0<(q:ℝ) ∧ (q:ℝ)<1 ∧
      q∈(ρ:Measure OrderPoint).support ∧ ∀ t∈(ρ:Measure OrderPoint).support,t≤q := by
  have hbp : 0<β := by exact_mod_cast (zero_lt_one.trans hβ)
  obtain ⟨q,hq⟩ := (ρ:Measure OrderPoint).isClosed_support.isCompact.exists_isGreatest
    ((ρ:Measure OrderPoint).nonempty_support (by exact NeZero.ne _))
  have h1 : (q:ℝ)<1 := lt_of_le_of_ne q.property.2 (by
    intro he
    apply minimizingParisi_one_not_mem_support hW hbp hρ
    simpa only [show q=(⟨1,by simp⟩ : OrderPoint) from Subtype.ext he] using hq.1)
  have h0 : 0<(q:ℝ) := by
    by_contra hn
    have hz : (q:ℝ)=0 := le_antisymm (not_lt.mp hn) q.property.1
    have hb : ∀ᵐ t : OrderPoint ∂(ρ:Measure OrderPoint),(t:ℝ)≤(0:ℝ) := by
      filter_upwards [(ρ:Measure OrderPoint).support_mem_ae] with t ht
      exact le_trans (show (t:ℝ)≤q from hq.2 ht) (hz.le)
    have hi : (∫ t : OrderPoint,(t:ℝ) ∂(ρ:Measure OrderPoint))≤0 :=
      integral_nonpos_of_ae hb
    exact (not_lt_of_ge hi) (minimizingParisi_mean_pos β hβ hρ)
  exact ⟨q,h0,h1,hq.1,hq.2⟩

 

theorem minimizingParisi_diffusion_square (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {t : OrderPoint} (ht : t∈(ρ:Measure OrderPoint).support) :
    (∫ ω,(fieldGradient β (measureCoefficient ρ β) ⟨t,t.property.1⟩
      (ParisiPath.solution ((ofMeasure β ρ).driftData hβ) (brownianPath W ω) t))^2 ∂P)=(t:ℝ) := by
  have hh := minimizingParisi_selfConsistency hW hβ hρ ht
  change (∫ ω,((ofMeasure β ρ).spin
    (solution ((ofMeasure β ρ).driftData hβ) (brownianPath W ω)) t)*
    ((ofMeasure β ρ).spin (solution ((ofMeasure β ρ).driftData hβ) (brownianPath W ω)) t) ∂P)=_ at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [spin_eq _ _ _ t.property,extend_of_mem _ t.property]
  have he : Real.toNNReal (t:ℝ)=(⟨t,t.property.1⟩ : ℝ≥0) := by
    apply NNReal.coe_injective
    exact Real.coe_toNNReal _ t.property.1
  simp only [ofMeasure,pow_two,he]

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
namespace ParisiFinite
open ParisiPath BoundedCoefficient

lemma measureCoefficient_after_support (ρ : ProbabilityMeasure OrderPoint) (β : ℝ≥0)
    (q : OrderPoint) (hq : ∀ t∈(ρ:Measure OrderPoint).support,t≤q)
    (r : ℝ≥0) (hr : (q:ℝ)≤r) : measureCoefficient ρ β r=β := by
  have he : {x : OrderPoint | (x:ℝ)≤r}=ᵐ[(ρ:Measure OrderPoint)] univ := by
    filter_upwards [(ρ:Measure OrderPoint).support_mem_ae] with x hx
    change ((x:ℝ)≤r) = True
    exact propext (iff_true_intro ((show (x:ℝ)≤q from hq x hx).trans hr))
  have hm : (ρ:Measure OrderPoint).real {x : OrderPoint | (x:ℝ)≤r}=1 := by
    rw [Measure.real,measure_congr he,measure_univ,ENNReal.toReal_one]
  simp [measureCoefficient,hm]

lemma dyadicSchedule_congr_future {γ δ : ℝ≥0 → ℝ≥0} {q : ℝ≥0}
    (h : ∀ r,q≤r → γ r=δ r) (u : Bool) (t d : ℝ≥0) (ht : q≤t) (n : ℕ) :
    dyadicSchedule γ u t d n=dyadicSchedule δ u t d n := by
  induction n generalizing t d with
  | zero =>
    simp only [dyadicSchedule]
    rw [h _ (by split_ifs; exact ht.trans (le_add_of_nonneg_right d.2); exact ht)]
  | succ n ih =>
    simp only [dyadicSchedule]
    rw [ih t (d/2) ht,ih (t+d/2) (d/2) (ht.trans (le_add_of_nonneg_right (by positivity)))]

lemma field_final_plateau (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (q : ℝ≥0) (hq : q≤1) (h : ∀ r,q≤r → γ r=β) (x : ℝ) :
    field β γ q x=terminal β x+(β:ℝ)*(1-(q:ℝ))/2 := by
  have he : field β γ q x=dyadicEvolution (fun _ => β) q (1-q) (terminal β) x := by
    unfold field dyadicEvolution
    apply congrArg sSup
    apply congrArg Set.range
    funext n
    rw [dyadicSchedule_congr_future h false q (1-q) le_rfl n]
  rw [he,dyadicEvolution_constant (terminal_lipschitz (β := (β:ℝ)) hβ) β q (1-q) x,step_terminal (β := (β:ℝ)) hβ,
    Real.sq_sqrt (NNReal.coe_nonneg _),NNReal.coe_sub hq,NNReal.coe_one]

lemma fieldGradient_final_plateau (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (q : ℝ≥0) (hq : q≤1) (h : ∀ r,q≤r → γ r=β) (x : ℝ) :
    fieldGradient β γ q x=Real.tanh ((β:ℝ)*x) := by
  unfold fieldGradient
  have he : field β γ q=fun y => terminal β y+(β:ℝ)*(1-(q:ℝ))/2 :=
    funext (field_final_plateau β hβ q hq h)
  rw [he]
  exact ((hasDerivAt_terminal hβ x).add_const _).deriv

lemma fieldCurvature_final_plateau (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (q : ℝ≥0) (hq : q≤1) (h : ∀ r,q≤r → γ r=β) (x : ℝ) :
    fieldCurvature β γ q x=(β:ℝ)*(1-(fieldGradient β γ q x)^2) := by
  have he : fieldGradient β γ q=fun y => Real.tanh ((β:ℝ)*y) :=
    funext (fieldGradient_final_plateau β hβ q hq h)
  rw [fieldCurvature,he]
  rw [(hasDerivAt_tanh_scaled β x).deriv]
  exact terminal_curvature_identity β hβ x

end ParisiFinite

namespace ParisiFinite
open ParisiPath BoundedCoefficient
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
variable {β : ℝ≥0}

 

theorem minimizingParisi_endpoint_bound (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {q : OrderPoint} (hq : q∈(ρ:Measure OrderPoint).support)
    (hqmax : ∀ t∈(ρ:Measure OrderPoint).support,t≤q)
    (h0 : 0<(q:ℝ)) (h1 : (q:ℝ)<1) : 1-(q:ℝ)≤1/(β:ℝ) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let c := ofMeasure β ρ
  let X (ω : Ω) := solution (c.driftData hβ) (brownianPath W ω)
  let a (ω : Ω) := c.curvature (X ω) q
  let m (ω : Ω) := c.spin (X ω) q
  have ha : Integrable a P := Integrable.of_bound
    (c.curvature_aestronglyMeasurable hW hβ _ q) (β:ℝ)
    (ae_of_all _ fun ω => c.norm_curvature_le hβ (X ω) q)
  have ha2 : Integrable (fun ω => (a ω)^2) P := c.curvature_square_integrable hW hβ _ q
  have hm2 : Integrable (fun ω => (m ω)^2) P := by
    simpa only [pow_two] using c.spin_product_integrable hW c hβ (c.driftData hβ) q
  have hms : (∫ ω,(m ω)^2 ∂P)=(q:ℝ) := by
    simpa only [expectedProduct,pow_two] using minimizingParisi_selfConsistency hW hβ hρ hq
  have hp : ∀ r : ℝ≥0,Real.toNNReal (q:ℝ)≤r → measureCoefficient ρ β r=β := by
    intro r hr
    apply measureCoefficient_after_support ρ β q hqmax r
    exact (Real.coe_toNNReal _ q.property.1).symm.le.trans (NNReal.coe_le_coe.mpr hr)
  have hae (ω : Ω) : a ω=(β:ℝ)*(1-(m ω)^2) := by
    dsimp only [a,m]
    rw [curvature_eq _ _ _ q.property,spin_eq _ _ _ q.property]
    exact fieldCurvature_final_plateau β hβ (Real.toNNReal q)
      (by exact_mod_cast (show (Real.toNNReal (q:ℝ):ℝ)≤1 by rw [Real.coe_toNNReal _ q.property.1];exact q.property.2)) hp _
  have ham : (∫ ω,a ω ∂P)=(β:ℝ)*(1-(q:ℝ)) := by
    simp_rw [hae]
    rw [integral_const_mul,integral_sub (integrable_const (1:ℝ)) hm2,
      integral_const,probReal_univ,one_smul,hms]
  let A : ℝ := ∫ ω,a ω ∂P
  have hv : A^2≤∫ ω,(a ω)^2 ∂P := by
    have hnon : 0≤∫ ω,(a ω-A)^2 ∂P := integral_nonneg fun ω => sq_nonneg _
    have he : (fun ω => (a ω-A)^2)=(fun ω => (a ω)^2-2*A*a ω+A^2) := by funext ω;ring
    have hi : Integrable (fun ω => (a ω)^2-2*A*a ω) P := ha2.sub (ha.const_mul (2*A))
    rw [he,integral_add hi (integrable_const (A^2)),
      integral_sub (f := fun ω => (a ω)^2) (g := fun ω => 2*A*a ω) ha2 (ha.const_mul (2*A)),
      integral_const_mul,integral_const,probReal_univ,one_smul] at hnon
    change 0≤(∫ ω,(a ω)^2 ∂P)-2*A*A+A^2 at hnon
    nlinarith
  have hr : (∫ ω,(a ω)^2 ∂P)≤1 := minimizingParisi_replicon hW hβ hρ hq h0 h1
  have hb : (β:ℝ)*(1-(q:ℝ))≤1 := by
    change (∫ ω,a ω ∂P)^2≤_ at hv
    rw [ham] at hv
    nlinarith
  exact (le_div_iff₀ (show (0:ℝ)<β from hβ)).mpr (by simpa only [mul_comm] using hb)

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
namespace ParisiFinite
open ParisiPath BoundedCoefficient

lemma measureCoefficient_before_support (ρ : ProbabilityMeasure OrderPoint) (β : ℝ≥0)
    (q : OrderPoint) (hq : ∀ t∈(ρ:Measure OrderPoint).support,q≤t)
    (r : ℝ≥0) (hr : (r:ℝ)<q) : measureCoefficient ρ β r=0 := by
  have he : {x : OrderPoint | (x:ℝ)≤r}=ᵐ[(ρ:Measure OrderPoint)] (∅ : Set OrderPoint) := by
    filter_upwards [(ρ:Measure OrderPoint).support_mem_ae] with x hx
    change ((x:ℝ)≤r) = False
    exact propext (iff_false_intro (not_le.mpr (hr.trans_le (hq x hx))))
  have hm : (ρ:Measure OrderPoint) {x : OrderPoint | (x:ℝ)≤r}=0 := by
    rw [measure_congr he,measure_empty]
  simp [measureCoefficient,hm,Measure.real]

lemma dyadicSchedule_congr_initial {γ δ : ℝ≥0 → ℝ≥0} {q : ℝ≥0}
    (h : ∀ r,r<q → γ r=δ r) (t d : ℝ≥0) (hd : 0<d) (ht : t+d≤q) (n : ℕ) :
    dyadicSchedule γ false t d n=dyadicSchedule δ false t d n := by
  induction n generalizing t d with
  | zero =>
    simp only [dyadicSchedule,Bool.false_eq_true,↓reduceIte]
    rw [h t (lt_of_lt_of_le (lt_add_of_pos_right t hd) ht)]
  | succ n ih =>
    simp only [dyadicSchedule]
    rw [ih t (d/2) (by positivity) (by nlinarith),
      ih (t+d/2) (d/2) (by positivity) (by nlinarith)]

lemma field_lipschitz (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (_ : ∀ s,γ s≤β) (t : ℝ≥0) :
    LipschitzWith 1 (field β γ t) :=
  dyadicEvolution_lipschitz (terminal_lipschitz hβ) hγ t (1-t)

lemma field_initial_heat (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ s,γ s≤β) {q : ℝ≥0} (hq : q≤1)
    (hg : ∀ s,s<q → γ s=0) {t : ℝ≥0} (ht : t<q) (x : ℝ) :
    field β γ t x=step 0 (Real.sqrt (q-t)) (field β γ q) x := by
  rw [field_DPP β hβ hγ hb ht.le hq]
  have he : dyadicEvolution γ t (q-t) (field β γ q) x=
      dyadicEvolution (fun _ => 0) t (q-t) (field β γ q) x := by
    unfold dyadicEvolution
    apply congrArg sSup
    apply congrArg Set.range
    funext n
    rw [dyadicSchedule_congr_initial hg t (q-t) (tsub_pos_iff_lt.mpr ht)
      (by rw [add_tsub_cancel_of_le ht.le]) n]
  rw [he,dyadicEvolution_constant (field_lipschitz β hβ hγ hb q) 0 t (q-t) x,NNReal.coe_sub ht.le]
  rfl

lemma hasDerivAt_step_mean {L C : ℝ≥0} {f g : ℝ → ℝ}
    (hf : LipschitzWith L f) (hg : Continuous g) (hd : ∀ x,HasDerivAt f (g x) x)
    (hb : ∀ x,‖g x‖≤C) (s x : ℝ) :
    HasDerivAt (step 0 s f) (step 0 s g x) x := by
  have he : step 0 s f=(fun y => ∫ z,f (y+s*z) ∂gaussianReal 0 1) := funext (step_mean s f)
  rw [he,step_mean]
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball x 1) (bound := fun _ => (C:ℝ))
    (F' := fun y z => g (y+s*z))
    (Metric.ball_mem_nhds _ zero_lt_one) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun y =>
      (hf.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
  · exact integrable_shift hf x s
  · exact (hg.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
  · exact ae_of_all _ fun z y _ => hb _
  · exact integrable_const _
  · exact ae_of_all _ fun z y _ => by
      convert! (hd (y+s*z)).comp y ((hasDerivAt_id y).add_const (s*z)) using 1
      first | rfl | simp only [mul_one]

lemma fieldGradient_initial_heat (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ s,γ s≤β) {q : ℝ≥0} (hq : q≤1)
    (hg : ∀ s,s<q → γ s=0) {t : ℝ≥0} (ht : t<q) (x : ℝ) :
    fieldGradient β γ t x=step 0 (Real.sqrt (q-t)) (fieldGradient β γ q) x := by
  have he : field β γ t=step 0 (Real.sqrt (q-t)) (field β γ q) :=
    funext (field_initial_heat β hβ hγ hb hq hg ht)
  apply (hasDerivAt_field β hβ hγ hb t x).unique
  rw [he]
  exact hasDerivAt_step_mean (C:=1) (field_lipschitz β hβ hγ hb q)
      (fieldGradient_lipschitz β hβ hγ hb q).continuous
      (hasDerivAt_field β hβ hγ hb q)
      (fun y => by simpa only [Real.norm_eq_abs,NNReal.coe_one] using fieldGradient_bound β hβ hγ hb q y)
      (Real.sqrt (q-t)) x

lemma fieldCurvature_initial_heat (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ s,γ s≤β) {q : ℝ≥0} (hq : q≤1)
    (hg : ∀ s,s<q → γ s=0) {t : ℝ≥0} (ht : t<q) (x : ℝ) :
    fieldCurvature β γ t x=step 0 (Real.sqrt (q-t)) (fieldCurvature β γ q) x := by
  have he : fieldGradient β γ t=step 0 (Real.sqrt (q-t)) (fieldGradient β γ q) :=
    funext (fieldGradient_initial_heat β hβ hγ hb hq hg ht)
  apply (hasDerivAt_fieldGradient β hβ hγ hb t x).unique
  rw [he]
  exact hasDerivAt_step_mean (C:=β) (fieldGradient_lipschitz β hβ hγ hb q)
      (fieldCurvature_lipschitz β hβ hγ hb q).continuous
      (hasDerivAt_fieldGradient β hβ hγ hb q)
      (fun y => by simpa only [Real.norm_eq_abs] using fieldCurvature_abs β hβ hγ hb q y)
      (Real.sqrt (q-t)) x

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
namespace ParisiFinite

lemma bounded_lipschitz_square {L C : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hb : ∀ x,‖f x‖≤C) :
    LipschitzWith (2*C*L) (fun x => f x^2) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  have he : f x^2-f y^2=(f x-f y)*(f x+f y) := by ring
  rw [he,norm_mul]
  have hu : ‖f x+f y‖≤2*(C:ℝ) := (norm_add_le _ _).trans (by linarith [hb x,hb y])
  calc
    _ ≤ ((L:ℝ)*‖x-y‖)*(2*(C:ℝ)) := mul_le_mul (hf.norm_sub_le x y) hu (norm_nonneg _) (by positivity)
    _ = _ := by simp only [NNReal.coe_mul,NNReal.coe_ofNat];ring

lemma step_mean_square_le {L C : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hb : ∀ x,‖f x‖≤C) (s x : ℝ) :
    (step 0 s f x)^2 ≤ step 0 s (fun y => f y^2) x := by
  have hm : MemLp (fun z => f (x+s*z)) 2 (gaussianReal 0 1) :=
    MemLp.of_bound (hf.continuous.comp (by fun_prop)).aestronglyMeasurable (C:ℝ)
      (ae_of_all _ fun z => hb _)
  have hh := variance_nonneg (X := fun z => f (x+s*z)) (μ := gaussianReal 0 1)
  rw [variance_eq_sub hm] at hh
  simp only [Pi.pow_apply] at hh
  simp only [step_mean]
  linarith

lemma fieldCurvature_square_lipschitz (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ s,γ s≤β) (t : ℝ≥0) :
    LipschitzWith (2*β*(5*β^2)) (fun x => fieldCurvature β γ t x^2) :=
  bounded_lipschitz_square (fieldCurvature_lipschitz β hβ hγ hb t)
    (fun x => fieldCurvature_abs β hβ hγ hb t x)

lemma initial_heat_curvature_square_le (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ s,γ s≤β) {q : ℝ≥0} (hq : q≤1)
    (hg : ∀ s,s<q → γ s=0) {t : ℝ≥0} (ht : t≤q) :
    step 0 (Real.sqrt t) (fun x => fieldCurvature β γ t x^2) 0≤
      step 0 (Real.sqrt q) (fun x => fieldCurvature β γ q x^2) 0 := by
  rcases ht.eq_or_lt with rfl|ht
  · exact le_rfl
  have hh (x : ℝ) : fieldCurvature β γ t x^2≤
      step 0 (Real.sqrt ((q:ℝ)-(t:ℝ))) (fun y => fieldCurvature β γ q y^2) x := by
    rw [fieldCurvature_initial_heat β hβ hγ hb hq hg ht]
    exact step_mean_square_le (C:=β) (fieldCurvature_lipschitz β hβ hγ hb q)
      (fun y => fieldCurvature_abs β hβ hγ hb q y) _ _
  have hl := step_le_of_le (fieldCurvature_square_lipschitz β hβ hγ hb t)
    (step_lipschitz (fieldCurvature_square_lipschitz β hβ hγ hb q) (le_refl 0)
      (Real.sqrt ((q:ℝ)-(t:ℝ)))) (le_refl 0) (Real.sqrt t) 0 hh
  rw [step_semigroup (fieldCurvature_square_lipschitz β hβ hγ hb q),
    Real.sq_sqrt t.coe_nonneg,Real.sq_sqrt (sub_nonneg.mpr (NNReal.coe_le_coe.mpr ht.le)),
    add_sub_cancel] at hl
  exact hl

lemma step_mean_zero_eq_gaussian_integral {f : ℝ → ℝ} (hf : Measurable f) (t : ℝ≥0) :
    step 0 (Real.sqrt t) f 0=∫ x,f x ∂gaussianReal 0 t := by
  have hm : (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt t*z)=gaussianReal 0 t := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      change (Real.sqrt t)^2 * 1 = (t:ℝ)
      rw [Real.sq_sqrt t.coe_nonneg,mul_one]
  rw [step_mean]
  simp only [zero_add]
  rw [←integral_map (by fun_prop) hf.aestronglyMeasurable,hm]

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
namespace ParisiFinite
open ParisiPath
namespace BoundedCoefficient
variable {β : ℝ≥0}

lemma solution_initial_heat (c : BoundedCoefficient β) (hβ : 0<β)
    {q : ℝ≥0} (hg : ∀ s,s<q → c.val s=0) (V : Path)
    (t : Time) (ht : (t:ℝ)≤q) : solution (c.driftData hβ) V t=V t := by
  rw [solution_eq]
  have hi : (∫ s in (0:ℝ)..(t:ℝ),
      (c.driftData hβ).val s (extend (solution (c.driftData hβ) V) s))=0 := by
    calc
      _ = ∫ s in (0:ℝ)..(t:ℝ),(0:ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le t.property.1
        intro s hs
        have hsq : Real.toNNReal s<q := by
          apply NNReal.coe_lt_coe.mp
          rw [Real.coe_toNNReal _ hs.1.le]
          exact hs.2.trans_le ht
        simp only [driftData,drift,real,hg _ hsq,NNReal.coe_zero,zero_mul]
      _ = 0 := by simp
  rw [hi,add_zero]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma expectedSquareCurvature_initial_heat (hW : IsBrownianReal W P)
    (c : BoundedCoefficient β) (hβ : 0<β) {q : ℝ≥0} (hq : q≤1)
    (hg : ∀ s,s<q → c.val s=0) {t : ℝ≥0} (ht : t≤q) :
    c.expectedSquareCurvature P W hβ t=
      step 0 (Real.sqrt t) (fun x => fieldCurvature β c.val t x^2) 0 := by
  rw [step_mean_zero_eq_gaussian_integral
    (fieldCurvature_square_lipschitz β hβ c.mono c.bound t).continuous.measurable]
  calc
    _ = ∫ ω,(fieldCurvature β c.val t (W t ω))^2 ∂P := by
      apply integral_congr_ae
      filter_upwards [brownianPath_eq_ae hW] with ω hω
      have ht1 : (t:ℝ)≤1 := by exact_mod_cast ht.trans hq
      rw [curvature_eq _ _ _ ⟨t.coe_nonneg,ht1⟩,extend_of_mem _ ⟨t.coe_nonneg,ht1⟩,
        c.solution_initial_heat hβ hg _ _ (by exact_mod_cast ht),hω]
      simp only [Real.toNNReal_coe]
      rfl
    _ = _ := (hW.hasLaw_eval t).integral_comp
      (fieldCurvature_square_lipschitz β hβ c.mono c.bound t).continuous.aestronglyMeasurable

lemma expectedSquareCurvature_initial_le (hW : IsBrownianReal W P)
    (c : BoundedCoefficient β) (hβ : 0<β) {q : ℝ≥0} (hq : q≤1)
    (hg : ∀ s,s<q → c.val s=0) {t : ℝ≥0} (ht : t≤q) :
    c.expectedSquareCurvature P W hβ t≤c.expectedSquareCurvature P W hβ q := by
  rw [c.expectedSquareCurvature_initial_heat hW hβ hq hg ht,
    c.expectedSquareCurvature_initial_heat hW hβ hq hg le_rfl]
  exact initial_heat_curvature_square_le β hβ c.mono c.bound hq hg ht

lemma expectedSquareCurvature_zero (hW : IsBrownianReal W P)
    (c : BoundedCoefficient β) (hβ : 0<β) :
    c.expectedSquareCurvature P W hβ 0=fieldCurvature β c.val 0 0^2 := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  calc
    _ = ∫ ω,(fieldCurvature β c.val 0 0)^2 ∂P := by
      apply integral_congr_ae
      filter_upwards [brownianPath_eq_ae hW,hW.eval_zero_ae_eq_zero] with ω hω h0
      rw [curvature_eq _ _ _ (by simp),extend_of_mem _ (by simp),solution_zero,hω]
      convert! congrArg (fun z => fieldCurvature β c.val 0 z^2) h0 using 1
      simp only [Real.toNNReal_zero]
      rfl
    _ = _ := by simp

end BoundedCoefficient
end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
namespace ParisiFinite

lemma fieldCurvature_not_constant (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ s,γ s≤β) (t : ℝ≥0) :
    ¬∃ k : ℝ,∀ x,fieldCurvature β γ t x=k := by
  rintro ⟨k,hk⟩
  have hk0 : 0<k := by rw [←hk 0];exact (fieldCurvature_bounds β hβ hγ hb t 0).1
  let f : ℝ → ℝ := fun x => fieldGradient β γ t x-k*x
  have hd (x : ℝ) : HasDerivAt f 0 x := by
    convert! (hasDerivAt_fieldGradient β hβ hγ hb t x).sub
      ((hasDerivAt_id x).const_mul k) using 1
    simp [hk]
  have he := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) (3/k) 0
  have hk3 : k*(3/k)=3 := by field_simp
  dsimp only [f] at he
  rw [hk3,mul_zero,sub_zero] at he
  have hb1 := (abs_le.mp (fieldGradient_bound β hβ hγ hb t (3/k))).2
  have hb0 := (abs_le.mp (fieldGradient_bound β hβ hγ hb t 0)).1
  linarith

lemma fieldCurvature_gaussian_variance_pos (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ s,γ s≤β) (t : ℝ≥0) {q : ℝ≥0} (hq : q≠0) :
    0<variance (fieldCurvature β γ t) (gaussianReal 0 q) := by
  have hc := (fieldCurvature_lipschitz β hβ hγ hb t).continuous
  have hm : MemLp (fieldCurvature β γ t) 2 (gaussianReal 0 q) :=
    MemLp.of_bound hc.aestronglyMeasurable (β:ℝ)
      (ae_of_all _ fun x => fieldCurvature_abs β hβ hγ hb t x)
  apply lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm ?_)
  intro hz
  have he := ae_eq_integral_of_variance_eq_zero hm hz
  let : Measure.IsOpenPosMeasure (gaussianReal 0 q) :=
    (gaussianReal_absolutelyContinuous' 0 hq).isOpenPosMeasure
  have hf := Measure.eq_of_ae_eq he hc continuous_const
  exact fieldCurvature_not_constant β hβ hγ hb t
    ⟨∫ x,fieldCurvature β γ t x ∂gaussianReal 0 q,fun x => congrFun hf x⟩

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
namespace ParisiFinite
open ParisiPath BoundedCoefficient
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
variable {β : ℝ≥0}

lemma minimizingParisi_least_support_eq_zero (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {q : OrderPoint} (hqs : q∈(ρ:Measure OrderPoint).support)
    (hqleast : ∀ t∈(ρ:Measure OrderPoint).support,q≤t) : (q:ℝ)=0 := by
  by_contra hq0
  have hqp : 0<(q:ℝ) := lt_of_le_of_ne q.property.1 (Ne.symm hq0)
  have hq1 : (q:ℝ)<1 := lt_of_le_of_ne q.property.2 (by
    intro he
    apply minimizingParisi_one_not_mem_support hW hβ hρ
    simpa only [show q=(⟨1,by simp⟩ : OrderPoint) from Subtype.ext he] using hqs)
  let r : ℝ≥0 := ⟨q,q.property.1⟩
  let c := ofMeasure β ρ
  let f : ℝ → ℝ := c.expectedSquareCurvature P W hβ
  have hr0 : 0<r := hqp
  have hr1 : r≤1 := by exact_mod_cast hq1.le
  have hg : ∀ s,s<r → c.val s=0 := fun s hs =>
    measureCoefficient_before_support ρ β q hqleast s hs
  have hf : Continuous f := c.expectedSquareCurvature_continuous hW hβ
  have hfq_le : f q≤1 := minimizingParisi_replicon hW hβ hρ hqs hqp hq1
  have hu (t : ℝ) (ht : t∈Icc (0:ℝ) (q:ℝ)) : f t≤1 := by
    have ht' : Real.toNNReal t≤r := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ ht.1]
      exact ht.2
    have hh := c.expectedSquareCurvature_initial_le hW hβ hr1 hg ht'
    rw [Real.coe_toNNReal _ ht.1] at hh
    exact hh.trans hfq_le
  have hi : (∫ t in (0:ℝ)..(q:ℝ),f t)=(q:ℝ) := by
    rw [←c.spin_mean_square_evolution hW hβ q ⟨hqp,hq1⟩]
    exact minimizingParisi_selfConsistency hW hβ hρ hqs
  have he (t : ℝ) (ht : t∈Icc (0:ℝ) (q:ℝ)) : f t=1 := by
    by_contra hn
    have hlt : f t<1 := lt_of_le_of_ne (hu t ht) hn
    have hh := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hqp hf.continuousOn (continuous_const.continuousOn : ContinuousOn (fun _ : ℝ => (1:ℝ)) _)
      (fun x hx => hu x ⟨hx.1.le,hx.2⟩) ⟨t,ht,hlt⟩
    rw [hi] at hh
    simp at hh
  have hzero : f 0=1 := he 0 ⟨le_rfl,hqp.le⟩
  have htop : f q=1 := he q ⟨hqp.le,le_rfl⟩
  let a := fieldCurvature β c.val r
  have ha := (fieldCurvature_lipschitz β hβ c.mono c.bound r).continuous
  have hm : MemLp a 2 (gaussianReal 0 r) := MemLp.of_bound ha.aestronglyMeasurable (β:ℝ)
    (ae_of_all _ fun x => fieldCurvature_abs β hβ c.mono c.bound r x)
  have hmean : fieldCurvature β c.val 0 0=∫ x,a x ∂gaussianReal 0 r := by
    have hh := fieldCurvature_initial_heat β hβ c.mono c.bound hr1 hg hr0 0
    simpa only [NNReal.coe_zero,sub_zero,step_mean_zero_eq_gaussian_integral ha.measurable] using hh
  have hsq : f q=∫ x,a x^2 ∂gaussianReal 0 r := by
    have hh := c.expectedSquareCurvature_initial_heat hW hβ hr1 hg le_rfl
    rw [step_mean_zero_eq_gaussian_integral (f:=fun x => fieldCurvature β c.val r x^2)
      (show Measurable (fun x => fieldCurvature β c.val r x^2) from (ha.pow 2).measurable)] at hh
    exact hh
  have hz : fieldCurvature β c.val 0 0^2=1 := by
    rw [←c.expectedSquareCurvature_zero hW hβ]
    exact hzero
  have hv : 0<variance a (gaussianReal 0 r) :=
    fieldCurvature_gaussian_variance_pos β hβ c.mono c.bound r hr0.ne'
  rw [variance_eq_sub hm] at hv
  simp only [Pi.pow_apply] at hv
  rw [←hsq,←hmean,htop,hz,sub_self] at hv
  exact lt_irrefl 0 hv

 

theorem minimizingParisi_zero_mem_support (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ) :
    (⟨0,by simp⟩ : OrderPoint)∈(ρ:Measure OrderPoint).support := by
  obtain ⟨q,hq⟩ := (ρ:Measure OrderPoint).isClosed_support.isCompact.exists_isLeast
    ((ρ:Measure OrderPoint).nonempty_support (by exact NeZero.ne _))
  have hz := minimizingParisi_least_support_eq_zero hW hβ hρ hq.1 hq.2
  have he : q=(⟨0,by simp⟩ : OrderPoint) := Subtype.ext hz
  simpa only [he] using hq.1

end ParisiFinite

end

end OAI
