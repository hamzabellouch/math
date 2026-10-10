import Mathlib
import OAI.Probability.ParisiFinite.CoshCone

namespace OAI

/-! Parisi Conjugate Transport. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open MeasureTheory ProbabilityTheory Filter Set Real
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Set Real
open scoped Topology NNReal
namespace ParisiSpectral
open ParisiFinite

lemma CoshCone.neg_exp_positiveDefinite {b r : ℝ} {f : ℝ → ℝ}
    (hb : 0<b) (hc : CoshCone b (fun x => exp (b*f x))) (hr : 0≤r) :
    PositiveDefinite (fun x => exp (-r*f x)) := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simpa only [neg_zero,zero_mul,exp_zero] using PositiveDefinite.constant zero_le_one
  have hh := hc.neg_rpow_positiveDefinite (div_pos hr hb)
  convert! hh using 1
  funext x
  rw [rpow_def_of_pos (exp_pos _),log_exp]
  congr 1
  field_simp

lemma evolve_coshCone {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {b : ℝ} (_hb : 0<b) (hc : CoshCone b (fun x => exp (b*f x)))
    {a : ℝ} (ha : 0<a) (ls : Schedule) (ho : ParisiGuerra.OrderedFrom b a ls) :
    CoshCone a (fun x => exp (a*evolve ls f x)) := by
  induction ls generalizing a with
  | nil => exact CoshCone.exp_lower ha ho hc
  | cons l ls ih =>
    have hp : 0<(l.1:ℝ) := ha.trans_le ho.1
    have hh := (ih hp ho.2).heat
      ((continuous_const.mul (evolve_lipschitz hf ls).continuous).rexp) l.2
    apply CoshCone.exp_lower ha ho.1
    convert hh using 1
    funext x
    exact exp_step_heat (evolve_lipschitz hf ls) hp.ne' l.2 x

lemma evolve_neg_exp_positiveDefinite {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {b : ℝ} (hb : 0<b) (hc : CoshCone b (fun x => exp (b*f x)))
    {a r : ℝ} (_ha : 0≤a) (hr : 0≤r) (ls : Schedule)
    (ho : ParisiGuerra.OrderedFrom b a ls) (hra : r≤a) :
    PositiveDefinite (fun x => exp (-r*evolve ls f x)) := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simpa only [neg_zero,zero_mul,exp_zero] using PositiveDefinite.constant zero_le_one
  have hp : 0<a := hr.trans_le hra
  exact (evolve_coshCone hf hb hc hp ls ho).neg_exp_positiveDefinite hp hr.le

lemma linearEvolve_continuous_bound {L R : ℝ≥0} {f g : ℝ → ℝ}
    (hf : LipschitzWith L f) (hg : Continuous g) (hR : ∀ x,|g x|≤R)
    (ls : Schedule) : Continuous (linearEvolve f g ls) ∧ ∀ x,|linearEvolve f g ls x|≤R := by
  induction ls with
  | nil => exact ⟨hg,hR⟩
  | cons l ls ih =>
    exact ⟨continuous_tiltedMean (evolve_lipschitz hf ls) ih.1 ih.2 _ _,
      fun x => abs_tiltedMean_le (evolve_lipschitz hf ls) ih.1 ih.2 _ _ _⟩

lemma heat_eq_standard (d : ℝ≥0) {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    heat d g x = ∫ z,g (x+sqrt d*z) ∂gaussianReal 0 1 := by
  have hm : Measure.map (fun z : ℝ => sqrt d*z) (gaussianReal 0 1)=gaussianReal 0 d := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [sq_sqrt d.coe_nonneg]
  unfold heat
  rw [←hm,integral_map (by fun_prop)]
  exact (hg.comp (continuous_const.add continuous_id)).aestronglyMeasurable

lemma exp_step_all {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (a s x : ℝ) : exp (a*step a s f x)=expMass a s f x := by
  by_cases ha : a=0
  · simp [ha,expMass]
  · exact exp_step hf ha s x

lemma conjugate_tiltedMean {L : ℝ≥0} {f g : ℝ → ℝ}
    (hf : LipschitzWith L f) (hg : Continuous g)
    (a c : ℝ) (d : ℝ≥0) (x : ℝ) :
    exp (a*step c (sqrt d) f x)*tiltedMean c (sqrt d) f g x =
      exp (-(c-a)*step c (sqrt d) f x)*
        heat d (fun y => exp (c*f y)*g y) x := by
  have hc : Continuous (fun y => exp (c*f y)*g y) :=
    ((continuous_const.mul hf.continuous).rexp.mul hg)
  rw [heat_eq_standard d hc]
  change exp (a*step c (sqrt d) f x)*(expMoment c (sqrt d) f g x/expMass c (sqrt d) f x)=_
  rw [←exp_step_all hf c (sqrt d) x]
  have he : exp (a*step c (sqrt d) f x)/exp (c*step c (sqrt d) f x)=
      exp (-(c-a)*step c (sqrt d) f x) := by rw [←exp_sub];congr 1;ring
  rw [←mul_div_assoc,mul_div_right_comm,he]
  rfl

 

lemma conjugate_linearEvolve_positiveDefinite {L : ℝ≥0} {f ψ : ℝ → ℝ}
    (hf : LipschitzWith L f) (hψ : PositiveDefinite ψ) (hcψ : Continuous ψ)
    {b : ℝ} (hb : 0<b) (hcone : CoshCone b (fun x => exp (b*f x)))
    {a : ℝ} (ha : 0≤a) (ls : Schedule) (ho : ParisiGuerra.OrderedFrom b a ls) :
    PositiveDefinite (fun x => exp (a*evolve ls f x)*
      linearEvolve f (fun y => exp (-b*f y)*ψ y) ls x) := by
  have hterm := (hcone.neg_exp_positiveDefinite hb hb.le).mul hψ
  have hcterm : Continuous (fun y => exp (-b*f y)*ψ y) :=
    (continuous_const.mul hf.continuous).rexp.mul hcψ
  have hbound : ∀ x, |exp (-b*f x)*ψ x|≤Real.toNNReal (exp (-b*f 0)*ψ 0) := by
    intro x
    have hh := hterm.norm_le x
    simpa only [Real.norm_eq_abs,Real.coe_toNNReal _ hterm.at_zero] using hh
  induction ls generalizing a with
  | nil =>
    have hp := (hcone.neg_exp_positiveDefinite hb (sub_nonneg.mpr ho)).mul hψ
    convert! hp using 1
    funext x
    change exp (a*f x)*(exp (-b*f x)*ψ x)=_
    rw [←mul_assoc,←exp_add]
    congr 2
    ring
  | cons l ls ih =>
    have ht := ih l.1.coe_nonneg ho.2
    have hcont : Continuous (fun x => exp ((l.1:ℝ)*evolve ls f x)*
        linearEvolve f (fun y => exp (-b*f y)*ψ y) ls x) :=
      (continuous_const.mul (evolve_lipschitz hf ls).continuous).rexp.mul
        (linearEvolve_continuous_bound hf hcterm hbound ls).1
    have hp := ht.heat hcont l.2
    have he := evolve_neg_exp_positiveDefinite hf hb hcone l.1.coe_nonneg
      (sub_nonneg.mpr ho.1) (l::ls) ⟨le_rfl,ho.2⟩ (sub_le_self _ ha)
    convert! he.mul hp using 1
    funext x
    exact conjugate_tiltedMean (evolve_lipschitz hf ls)
      (linearEvolve_continuous_bound hf hcterm hbound ls).1 a l.1 l.2 x

end ParisiSpectral

 

 

open MeasureTheory ProbabilityTheory Filter Function Set ContinuousLinearMap
open scoped Topology NNReal Convolution
namespace ParisiFinite
open ParisiPath

lemma compact_convolution_bound {k g : ℝ → ℝ} (hk : HasCompactSupport k)
    (hkc : Continuous k) (hg : Continuous g) (R : ℝ≥0) (hR : ∀ x,|g x|≤R) (x : ℝ) :
    |(k ⋆[lsmul ℝ ℝ,volume] g) x|≤(∫ z,‖k z‖)*(R:ℝ) := by
  change |∫ z,k z*g (x-z)|≤_
  calc
    _ ≤ ∫ z,‖k z*g (x-z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z,‖k z‖*(R:ℝ) := by
      apply integral_mono (hk.convolutionExists_left (lsmul ℝ ℝ) hkc hg.locallyIntegrable x).norm
        (hkc.integrable_of_hasCompactSupport hk |>.norm.mul_const _)
      intro z
      dsimp only
      rw [lsmul_apply,smul_eq_mul,norm_mul,Real.norm_eq_abs (g (x-z))]
      exact mul_le_mul_of_nonneg_left (hR _) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

def boundedMollify (φ : ContDiffBump (0:ℝ)) {g : ℝ → ℝ} (hg : Continuous g)
    (R : ℝ≥0) (hR : ∀ x,|g x|≤R) : SmoothField where
  val := smoothConvolution φ g
  d1 := deriv (φ.normed volume) ⋆[lsmul ℝ ℝ,volume] g
  d2 := deriv (deriv (φ.normed volume)) ⋆[lsmul ℝ ℝ,volume] g
  hasD1 := φ.hasCompactSupport_normed.hasDerivAt_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed hg.locallyIntegrable
  hasD2 := φ.hasCompactSupport_normed.deriv.hasDerivAt_convolution_left (lsmul ℝ ℝ)
    (ContDiff.deriv' (φ.contDiff_normed (n:=2))) hg.locallyIntegrable
  continuousD2 := by
    apply φ.hasCompactSupport_normed.deriv.deriv.contDiff_convolution_left (lsmul ℝ ℝ)
      (ContDiff.deriv' (n:=1) (ContDiff.deriv' (n:=2) (φ.contDiff_normed (μ:=volume) (n:=3)))) hg.locallyIntegrable |>.continuous
  bound1 := ⟨(∫ z,‖deriv (φ.normed volume) z‖)*(R:ℝ),by positivity⟩
  bound2 := ⟨(∫ z,‖deriv (deriv (φ.normed volume)) z‖)*(R:ℝ),by positivity⟩
  normD1 := compact_convolution_bound φ.hasCompactSupport_normed.deriv
    (φ.contDiff_normed (n:=1) |>.continuous_deriv (by norm_num)) hg R hR
  normD2 := compact_convolution_bound φ.hasCompactSupport_normed.deriv.deriv
    (ContDiff.deriv' (n:=0) (ContDiff.deriv' (n:=1) (φ.contDiff_normed (μ:=volume) (n:=2))) |>.continuous) hg R hR

lemma boundedMollify_bound (φ : ContDiffBump (0:ℝ)) {g : ℝ → ℝ} (hg : Continuous g)
    (R : ℝ≥0) (hR : ∀ x,|g x|≤R) (x : ℝ) : |(boundedMollify φ hg R hR).val x|≤R :=
  by simpa only [boundedMollify,Real.norm_eq_abs] using smoothConvolution_bound φ hg hR x

lemma tiltedMean_tendsto_terminal {L R : ℝ≥0} {f g : ℝ → ℝ}
    (hf : LipschitzWith L f) {G : ℕ → ℝ → ℝ} (hGc : ∀ n,Continuous (G n))
    (hGR : ∀ n x,|G n x|≤R) (hG : ∀ x,Tendsto (fun n => G n x) atTop (𝓝 (g x)))
    (a s x : ℝ) : Tendsto (fun n => tiltedMean a s f (G n) x) atTop (𝓝 (tiltedMean a s f g x)) := by
  apply Tendsto.div_const
  apply tendsto_integral_of_dominated_convergence (fun z => Real.exp (a*f (x+s*z))*(R:ℝ))
  · intro n
    exact (((continuous_const.mul (hf.continuous.comp (continuous_const.add (continuous_const.mul continuous_id)))).rexp).mul
      ((hGc n).comp (continuous_const.add (continuous_const.mul continuous_id)))).aestronglyMeasurable
  · exact (integrable_exp_shift hf a x s).mul_const _
  · intro n
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hGR n _) (Real.exp_pos _).le
  · exact ae_of_all _ fun z => (hG _).const_mul _

lemma linearEvolve_tendsto_terminal {L R : ℝ≥0} {f g : ℝ → ℝ}
    (hf : LipschitzWith L f) {G : ℕ → ℝ → ℝ} (hGc : ∀ n,Continuous (G n))
    (hGR : ∀ n x,|G n x|≤R) (hG : ∀ x,Tendsto (fun n => G n x) atTop (𝓝 (g x)))
    (ls : Schedule) (x : ℝ) :
    Tendsto (fun n => linearEvolve f (G n) ls x) atTop (𝓝 (linearEvolve f g ls x)) := by
  induction ls generalizing x with
  | nil => exact hG x
  | cons l ls ih =>
    exact tiltedMean_tendsto_terminal (evolve_lipschitz hf ls)
      (fun n => (ParisiSpectral.linearEvolve_continuous_bound hf (hGc n) (hGR n) ls).1)
      (fun n => (ParisiSpectral.linearEvolve_continuous_bound hf (hGc n) (hGR n) ls).2) ih _ _ _

variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma generalSchedule_actual_transport_continuous (hW : IsBrownianReal W P)
    (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    (f : SmoothField) {g : ℝ → ℝ} (hg : Continuous g) (R : ℝ≥0) (hR : ∀ x, |g x|≤R)
    (ls : Schedule) (d : ℝ≥0) (hd0 : d≠0) (hd1 : d≤1)
    (hw : width ls=d)
    (hb : ∀ t∈Ioo (0:ℝ) d,∀ x,b.val t x=finiteTimeCoefficient ls 0 t*(scheduleField f ls 0 t).d1 x) :
    (∫ ω,g (solution b (brownianPath W ω)
      ⟨d,by exact ⟨d.coe_nonneg,by exact_mod_cast hd1⟩⟩) ∂P) = linearEvolve f.val g ls 0 := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let G (n : ℕ) := boundedMollify (shrinkingBump n) hg R hR
  let X (ω : Ω) := solution b (brownianPath W ω) ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩
  have hGR (n : ℕ) (x : ℝ) : |(G n).val x|≤R := boundedMollify_bound _ hg R hR x
  have ht (x : ℝ) : Tendsto (fun n => (G n).val x) atTop (𝓝 (g x)) := smoothConvolution_tendsto hg x
  have hi : Tendsto (fun n => ∫ ω,(G n).val (X ω) ∂P) atTop (𝓝 (∫ ω,g (X ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (R:ℝ))
    · intro n
      exact ((G n).continuousVal.measurable.comp_aemeasurable
        (aemeasurable_solution_eval _ _ (brownianPath_aemeasurable_eval hW) _)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hGR n (X ω)
    · exact ae_of_all _ fun ω => ht (X ω)
  have he (n : ℕ) : (∫ ω,(G n).val (X ω) ∂P)=linearEvolve f.val (G n).val ls 0 :=
    generalSchedule_actual_transport hW b hc f (G n) R (hGR n) ls d hd0 hd1 hw hb
  simp_rw [he] at hi
  exact tendsto_nhds_unique hi (linearEvolve_tendsto_terminal f.lipschitz
    (fun n => (G n).continuousVal) hGR ht ls 0)

end ParisiFinite

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiPath
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma brownian_solution_time_generator_between (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeQuadraticTest) (a c : ℝ≥0) (ha0 : a≠0) (hac : a<c) (hc1 : c≤1)
    (hb : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    (∫ ω,f.val c (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1⟩) ∂P)-
      (∫ ω,f.val a (solution b (brownianPath W ω) ⟨a,a.coe_nonneg,by exact_mod_cast hac.le.trans hc1⟩) ∂P)=
      ∫ t in (a:ℝ)..(c:ℝ),timeGeneratorC2 P W b f t+timeDerivativeC2 P W b f t := by
  have hi := (timeGeneratorC2_intervalIntegrable hW b f hb).add
    (timeDerivativeC2_intervalIntegrable hW b f hb)
  have hsub (d : ℝ≥0) (hd : d≤1) : uIcc (0:ℝ) d⊆uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le d.coe_nonneg,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl (by exact_mod_cast hd)
  have hsub' : uIcc (a:ℝ) c⊆uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le (by exact_mod_cast hac.le),uIcc_of_le zero_le_one]
    exact Icc_subset_Icc a.coe_nonneg (by exact_mod_cast hc1)
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hi.mono_set (hsub a (hac.le.trans hc1))) (hi.mono_set hsub')
  have ha := brownian_solution_time_generator_at hW b f a ha0 (hac.le.trans hc1) hb
  have hc := brownian_solution_time_generator_at hW b f c (ne_of_gt ((pos_iff_ne_zero.mpr ha0).trans hac)) hc1 hb
  rw [intervalIntegral.integral_add
    ((timeGeneratorC2_intervalIntegrable hW b f hb).mono_set (hsub a (hac.le.trans hc1)))
    ((timeDerivativeC2_intervalIntegrable hW b f hb).mono_set (hsub a (hac.le.trans hc1))),
    intervalIntegral.integral_add
    ((timeGeneratorC2_intervalIntegrable hW b f hb).mono_set (hsub c hc1))
    ((timeDerivativeC2_intervalIntegrable hW b f hb).mono_set (hsub c hc1))] at he
  linarith

end ParisiPath
namespace ParisiFinite
open ParisiPath ParisiSpectral
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma generalSchedule_terminal_comparison_between (hW : IsBrownianReal W P)
    (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    (f g : SmoothField) (ls : Schedule) (a c : ℝ≥0) (ha0 : a≠0) (hac : a<c) (hc1 : c≤1)
    (hw : (a:ℝ)+width ls=c)
    (hb : ∀ t∈Ioo (a:ℝ) c,∀ x,b.val t x=finiteTimeCoefficient ls a t*(scheduleField f ls a t).d1 x) :
    (∫ ω,g.val (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1⟩) ∂P)-
      (∫ ω,f.val (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1⟩) ∂P) ≤
    (∫ ω,(smoothEvolve g ls).val (solution b (brownianPath W ω) ⟨a,a.coe_nonneg,by exact_mod_cast hac.le.trans hc1⟩) ∂P)-
      (∫ ω,(smoothEvolve f ls).val (solution b (brownianPath W ω) ⟨a,a.coe_nonneg,by exact_mod_cast hac.le.trans hc1⟩) ∂P) := by
  let rf := generalScheduleTimeRealization f ls a a.coe_nonneg (by rw [hw];exact_mod_cast hc1)
  let rg := generalScheduleTimeRealization g ls a a.coe_nonneg (by rw [hw];exact_mod_cast hc1)
  have hf := brownian_solution_time_generator_between hW b rf.test a c ha0 hac hc1 hc
  have hg := brownian_solution_time_generator_between hW b rg.test a c ha0 hac hc1 hc
  have hsub : uIcc (a:ℝ) c⊆uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le (by exact_mod_cast hac.le),uIcc_of_le zero_le_one]
    exact Icc_subset_Icc a.coe_nonneg (by exact_mod_cast hc1)
  have hif := (timeGeneratorC2_intervalIntegrable hW b rf.test hc).add
    (timeDerivativeC2_intervalIntegrable hW b rf.test hc)
  have hig := (timeGeneratorC2_intervalIntegrable hW b rg.test hc).add
    (timeDerivativeC2_intervalIntegrable hW b rg.test hc)
  have hle : (∫ t in (a:ℝ)..(c:ℝ),timeGeneratorC2 P W b rg.test t+timeDerivativeC2 P W b rg.test t) ≤
      ∫ t in (a:ℝ)..(c:ℝ),timeGeneratorC2 P W b rf.test t+timeDerivativeC2 P W b rf.test t := by
    apply intervalIntegral.integral_mono_ae_restrict (by exact_mod_cast hac.le) (hig.mono_set hsub) (hif.mono_set hsub)
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (show ∀ᵐ t ∂volume,t≠(a:ℝ) from volume.ae_ne _),
      ae_restrict_of_ae (show ∀ᵐ t ∂volume,t≠(c:ℝ) from volume.ae_ne _)] with t ht hn0 hne
    have htt : t∈Ioo (a:ℝ) c := ⟨ht.1.lt_of_ne (Ne.symm hn0),ht.2.lt_of_ne hne⟩
    change (∫ ω,generatorC2 (rg.test.slice t) b t (extend (solution b (brownianPath W ω)) t) ∂P)+
        (∫ ω,rg.test.dt t (extend (solution b (brownianPath W ω)) t) ∂P) ≤
      (∫ ω,generatorC2 (rf.test.slice t) b t (extend (solution b (brownianPath W ω)) t) ∂P)+
        (∫ ω,rf.test.dt t (extend (solution b (brownianPath W ω)) t) ∂P)
    rw [←integral_add (generatorC2_integrable hW b _ t) (timeDerivativeC2_integrable_inner hW b rg.test t),
      ←integral_add (generatorC2_integrable hW b _ t) (timeDerivativeC2_integrable_inner hW b rf.test t)]
    apply integral_mono ((generatorC2_integrable hW b _ t).add (timeDerivativeC2_integrable_inner hW b rg.test t))
      ((generatorC2_integrable hW b _ t).add (timeDerivativeC2_integrable_inner hW b rf.test t))
    intro ω
    simp only [Pi.add_apply,generatorC2,TimeQuadraticTest.slice,rg.d1_eq,rg.d2_eq,rg.dt_eq,rf.d1_eq,rf.d2_eq,rf.dt_eq]
    rw [scheduleField_PDE g ls a t _ ht.1 (by simpa only [hw] using htt.2),
      scheduleField_PDE f ls a t _ ht.1 (by simpa only [hw] using htt.2),hb t htt]
    have hsquare := mul_nonneg (finiteTimeCoefficient_nonneg ls a t)
      (sq_nonneg ((scheduleField g ls a t).d1 (extend (solution b (brownianPath W ω)) t) -
        (scheduleField f ls a t).d1 (extend (solution b (brownianPath W ω)) t)))
    nlinarith [hsquare]
  rw [←hg,←hf] at hle
  have hef (x : ℝ) : rf.test.val c x=f.val x := by
    rw [rf.val_eq,scheduleField_after f ls a c x hw.le]
  have heg (x : ℝ) : rg.test.val c x=g.val x := by
    rw [rg.val_eq,scheduleField_after g ls a c x hw.le]
  simp_rw [hef,heg,rf.val_eq,rg.val_eq,scheduleField_start] at hle
  linarith

lemma hasDerivAt_expected_evolve_terminal [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Integrable X P) (f g : SmoothField) (R : ℝ≥0) (hR : ∀ x,|g.val x|≤R)
    (ls : Schedule) :
    HasDerivAt (fun u => ∫ ω,evolve ls (terminalPerturbation f g u).val (X ω) ∂P)
      (∫ ω,linearEvolve f.val g.val ls (X ω) ∂P) 0 := by
  let F := evolveFamily (terminalFamily f g R hR) ls
  have hd (u x : ℝ) : |F.dot u x|≤R := by
    rw [evolveFamily_dot]
    apply (linearEvolve_continuous_bound (terminalPerturbation f g u).lipschitz
      (g.continuousVal.const_mul (Real.cos u)) _ ls).2 x
    intro y
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_cos_le_one u) (hR y) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hi : HasDerivAt (fun u => ∫ ω,(F.field u).val (X ω) ∂P)
      (∫ ω,F.dot 0 (X ω) ∂P) 0 := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ)
      (bound:=fun _ : Ω => (R:ℝ)) (F':=fun u ω => F.dot u (X ω)) (by simp) ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Eventually.of_forall fun u => ((F.field u).lipschitz.continuous.measurable.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
    · rw [show (F.field 0).val = (smoothEvolve f ls).val by
        funext x;rw [evolveFamily_val,smoothEvolve_val];simp only [terminalFamily,SmoothField.directional,terminalPerturbation,Real.sin_zero,zero_mul,add_zero]]
      exact ((smoothEvolve f ls).staticTimeTest.slice 0).integrable_comp hX
    · exact ((F.continuousDot.comp (continuous_const.prodMk continuous_id)).measurable.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
    · exact ae_of_all _ fun ω u _ => by simpa only [Real.norm_eq_abs] using hd u (X ω)
    · exact integrable_const _
    · exact ae_of_all _ fun ω u _ => F.hasDot (X ω) u
  dsimp only [F] at hi
  simp_rw [evolveFamily_val,evolveFamily_dot] at hi
  simpa only [terminalFamily,SmoothField.directional,terminalPerturbation,Real.sin_zero,Real.cos_zero,zero_mul,add_zero,one_mul] using hi

lemma generalSchedule_actual_transport_between (hW : IsBrownianReal W P)
    (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    (f g : SmoothField) (R : ℝ≥0) (hR : ∀ x,|g.val x|≤R)
    (ls : Schedule) (a c : ℝ≥0) (ha0 : a≠0) (hac : a<c) (hc1 : c≤1)
    (hw : (a:ℝ)+width ls=c)
    (hb : ∀ t∈Ioo (a:ℝ) c,∀ x,b.val t x=finiteTimeCoefficient ls a t*(scheduleField f ls a t).d1 x) :
    (∫ ω,g.val (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1⟩) ∂P)=
      ∫ ω,linearEvolve f.val g.val ls
        (solution b (brownianPath W ω) ⟨a,a.coe_nonneg,by exact_mod_cast hac.le.trans hc1⟩) ∂P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let X : Ω → ℝ := fun ω => solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1⟩
  let Y : Ω → ℝ := fun ω => solution b (brownianPath W ω) ⟨a,a.coe_nonneg,by exact_mod_cast hac.le.trans hc1⟩
  let J := ∫ ω,g.val (X ω) ∂P
  let V : ℝ → ℝ := fun u => (∫ ω,evolve ls (terminalPerturbation f g u).val (Y ω) ∂P)-
    (∫ ω,evolve ls f.val (Y ω) ∂P)-Real.sin u*J
  have hX : Integrable X P := brownian_solution_integrable hW b _
  have hY : Integrable Y P := brownian_solution_integrable hW b _
  have hif : Integrable (fun ω => f.val (X ω)) P := (f.staticTimeTest.slice 0).integrable_comp hX
  have hig : Integrable (fun ω => g.val (X ω)) P := (g.staticTimeTest.slice 0).integrable_comp hX
  have hle (u : ℝ) : 0≤V u := by
    have hh := generalSchedule_terminal_comparison_between hW b hc f (terminalPerturbation f g u)
      ls a c ha0 hac hc1 hw hb
    change (∫ ω,f.val (X ω)+Real.sin u*g.val (X ω) ∂P)-(∫ ω,f.val (X ω) ∂P)≤_ at hh
    rw [integral_add hif (hig.const_mul _),integral_const_mul] at hh
    simp only [smoothEvolve_val] at hh
    dsimp only [V,J]
    linarith
  have he : V 0=0 := by
    simp only [V,terminalPerturbation,Real.sin_zero,zero_mul,add_zero,sub_self]
  have hm : IsLocalMin V 0 := by
    filter_upwards [] with u
    rw [he]
    exact hle u
  have hd : HasDerivAt V ((∫ ω,linearEvolve f.val g.val ls (Y ω) ∂P)-J) 0 := by
    have hh := ((hasDerivAt_expected_evolve_terminal hY f g R hR ls).sub_const
      (∫ ω,evolve ls f.val (Y ω) ∂P)).sub ((Real.hasDerivAt_sin 0).mul_const J)
    convert! hh using 1
    simp only [Real.cos_zero,one_mul]
  have hz := hm.hasDerivAt_eq_zero hd
  change J=_
  linarith

lemma generalSchedule_actual_transport_between_continuous (hW : IsBrownianReal W P)
    (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    (f : SmoothField) {g : ℝ → ℝ} (hg : Continuous g) (R : ℝ≥0) (hR : ∀ x,|g x|≤R)
    (ls : Schedule) (a c : ℝ≥0) (ha0 : a≠0) (hac : a<c) (hc1 : c≤1)
    (hw : (a:ℝ)+width ls=c)
    (hb : ∀ t∈Ioo (a:ℝ) c,∀ x,b.val t x=finiteTimeCoefficient ls a t*(scheduleField f ls a t).d1 x) :
    (∫ ω,g (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1⟩) ∂P)=
      ∫ ω,linearEvolve f.val g ls
        (solution b (brownianPath W ω) ⟨a,a.coe_nonneg,by exact_mod_cast hac.le.trans hc1⟩) ∂P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let G (n : ℕ) := boundedMollify (shrinkingBump n) hg R hR
  let X : Ω → ℝ := fun ω => solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1⟩
  let Y : Ω → ℝ := fun ω => solution b (brownianPath W ω) ⟨a,a.coe_nonneg,by exact_mod_cast hac.le.trans hc1⟩
  have hGR (n : ℕ) (x : ℝ) : |(G n).val x|≤R := boundedMollify_bound _ hg R hR x
  have hGc (n : ℕ) := (G n).continuousVal
  have ht (x : ℝ) : Tendsto (fun n => (G n).val x) atTop (𝓝 (g x)) := smoothConvolution_tendsto hg x
  have hx : Tendsto (fun n => ∫ ω,(G n).val (X ω) ∂P) atTop (𝓝 (∫ ω,g (X ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (R:ℝ))
    · intro n
      exact ((hGc n).measurable.comp_aemeasurable
        (aemeasurable_solution_eval _ _ (brownianPath_aemeasurable_eval hW) _)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hGR n (X ω)
    · exact ae_of_all _ fun ω => ht (X ω)
  have hy : Tendsto (fun n => ∫ ω,linearEvolve f.val (G n).val ls (Y ω) ∂P) atTop
      (𝓝 (∫ ω,linearEvolve f.val g ls (Y ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (R:ℝ))
    · intro n
      exact ((linearEvolve_continuous_bound f.lipschitz (hGc n) (hGR n) ls).1.measurable.comp_aemeasurable
        (aemeasurable_solution_eval _ _ (brownianPath_aemeasurable_eval hW) _)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using
        (linearEvolve_continuous_bound f.lipschitz (hGc n) (hGR n) ls).2 (Y ω)
    · exact ae_of_all _ fun ω => linearEvolve_tendsto_terminal f.lipschitz hGc hGR ht ls (Y ω)
  have he (n : ℕ) : (∫ ω,(G n).val (X ω) ∂P)=∫ ω,linearEvolve f.val (G n).val ls (Y ω) ∂P :=
    generalSchedule_actual_transport_between hW b hc f (G n) R (hGR n) ls a c ha0 hac hc1 hw hb
  simp_rw [he] at hx
  exact tendsto_nhds_unique hx hy

end ParisiFinite

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiPath
variable {K M : ℝ≥0}
lemma drift_comp_tendsto_at {B : ℕ → Drift K M} {b : Drift K M}
    {t : ℝ} (hB : ∀ x,Tendsto (fun n => (B n).val t x) atTop (𝓝 (b.val t x)))
    {X : ℕ → Path} {Y : Path} (hX : Tendsto X atTop (𝓝 Y)) :
    Tendsto (fun n => (B n).val t (extend (X n) t)) atTop (𝓝 (b.val t (extend Y t))) := by
  have hx : Tendsto (fun n => extend (X n) t) atTop (𝓝 (extend Y t)) :=
    (show Continuous (fun V : Path => extend V t) by unfold extend;fun_prop).continuousAt.tendsto.comp hX
  have hd : Tendsto (fun n => (B n).val t (extend (X n) t)-(B n).val t (extend Y t))
      atTop (𝓝 (0:ℝ)) := by
    have hnorm (n : ℕ) : ‖(B n).val t (extend (X n) t)-(B n).val t (extend Y t)‖ ≤
        (K:ℝ)*‖extend (X n) t-extend Y t‖ := by
      simpa only [←dist_eq_norm] using (B n).lipschitz t |>.dist_le_mul (extend (X n) t) (extend Y t)
    exact squeeze_zero_norm hnorm
      (by simpa only [sub_self,norm_zero,mul_zero] using
        ((hx.sub_const (extend Y t)).norm.const_mul (K:ℝ)))
  simpa only [sub_add_cancel,zero_add] using hd.add (hB (extend Y t))

lemma next_tendsto_drift_ae {B : ℕ → Drift K M} {b : Drift K M}
    (hB : ∀ᵐ t ∂volume, ∀ x,Tendsto (fun n => (B n).val t x) atTop (𝓝 (b.val t x)))
    {X : ℕ → Path} {Y : Path} (hX : Tendsto X atTop (𝓝 Y)) (W : Path) :
    Tendsto (fun n => next (B n) W (X n)) atTop (𝓝 (next b W Y)) := by
  let R (n : ℕ) (t : ℝ) : ℝ := ‖(B n).val t (extend (X n) t)-b.val t (extend Y t)‖
  have hRm (n : ℕ) : Measurable (R n) :=
    (((B n).measurable.comp (measurable_id.prodMk (continuous_extend (X n)).measurable)).sub
      (b.measurable.comp (measurable_id.prodMk (continuous_extend Y).measurable))).norm
  have hRb (n : ℕ) (t : ℝ) : R n t ≤ 2*(M:ℝ) :=
    (norm_sub_le _ _).trans (by linarith [(B n).bound t (extend (X n) t),b.bound t (extend Y t)])
  have hRi (n : ℕ) : IntervalIntegrable (R n) volume 0 1 :=
    (intervalIntegrable_const (c := 2*(M:ℝ))).mono_fun' (hRm n).aestronglyMeasurable
      (Eventually.of_forall fun t => by simpa only [R,norm_norm] using hRb n t)
  have he : Tendsto (fun n => ∫ t in (0:ℝ)..1,R n t) atTop (𝓝 (0:ℝ)) := by
    have hh := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (a := (0:ℝ)) (b := 1) (μ := volume) (l := atTop) (F := R) (f := fun _ => (0:ℝ))
      (fun _ => 2*(M:ℝ)) (Eventually.of_forall fun n => (hRm n).aestronglyMeasurable.restrict)
      (Eventually.of_forall fun n => ae_of_all _ fun t _ => by simpa only [R,norm_norm] using hRb n t)
      intervalIntegrable_const (by
        filter_upwards [hB] with t ht hit
        simpa only [R,sub_self,norm_zero] using ((drift_comp_tendsto_at ht hX).sub_const (b.val t (extend Y t))).norm)
    simpa only [intervalIntegral.integral_zero] using hh
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_) he
  apply (ContinuousMap.dist_le
    (intervalIntegral.integral_nonneg zero_le_one (fun t _ => norm_nonneg _))).mpr
  intro t
  rw [dist_eq_norm,next_apply,next_apply,add_sub_add_left_eq_sub,
    ←intervalIntegral.integral_sub (integrable_comp (B n) (X n) _ _) (integrable_comp b Y _ _)]
  calc
    _ ≤ ∫ s in (0:ℝ)..(t:ℝ),R n s := intervalIntegral.norm_integral_le_integral_norm t.property.1
    _ ≤ ∫ s in (0:ℝ)..1,R n s := intervalIntegral.integral_mono_interval le_rfl t.property.1
      t.property.2 (ae_of_all _ fun s => norm_nonneg _) (hRi n)

lemma iterate_tendsto_drift_ae {B : ℕ → Drift K M} {b : Drift K M}
    (hB : ∀ᵐ t ∂volume, ∀ x,Tendsto (fun n => (B n).val t x) atTop (𝓝 (b.val t x)))
    (W X : Path) (k : ℕ) :
    Tendsto (fun n => ((next (B n) W)^[k]) X) atTop (𝓝 (((next b W)^[k]) X)) := by
  induction k with
  | zero => exact tendsto_const_nhds
  | succ k ih => simpa only [iterate_succ_apply'] using next_tendsto_drift_ae hB ih W

 

theorem solution_tendsto_drift_ae {B : ℕ → Drift K M} {b : Drift K M}
    (hB : ∀ᵐ t ∂volume, ∀ x,Tendsto (fun n => (B n).val t x) atTop (𝓝 (b.val t x))) (W : Path) :
    Tendsto (fun n => solution (B n) W) atTop (𝓝 (solution b W)) := by
  obtain ⟨k,hk⟩ := (FloorSemiring.tendsto_pow_div_factorial_atTop (K:ℝ)).eventually
    (gt_mem_nhds zero_lt_one) |>.exists
  let C : ℝ≥0 := ⟨(K:ℝ)^k/k.factorial,by positivity⟩
  have hc (b' : Drift K M) : ContractingWith C ((next b' W)^[k]) :=
    ⟨hk,LipschitzWith.of_dist_le_mul fun X Y => dist_iterate b' W X Y k⟩
  have ht := iterate_tendsto_drift_ae hB W (solution b W) k
  rw [(solution_fixed b W).iterate k] at ht
  have hz : Tendsto (fun n => dist (solution b W) (((next (B n) W)^[k]) (solution b W))/(1-(C:ℝ)))
      atTop (𝓝 (0:ℝ)) := by
    simpa only [dist_self,zero_div] using ((tendsto_const_nhds (x := solution b W)).dist ht).div_const (1-(C:ℝ))
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hz
  rw [dist_comm]
  exact (hc (B n)).dist_le_of_fixedPoint _ ((solution_fixed (B n) W).iterate k)

end ParisiPath

end

end OAI
