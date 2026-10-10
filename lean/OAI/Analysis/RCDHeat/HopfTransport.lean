import Mathlib
import OAI.Analysis.RCDHeat.HopfHeat
import OAI.Analysis.RCDHeat.UpperLipschitzEnvelope

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: HopfTransport, HopfPath, L2Dominated, L2LipschitzPath, HopfL2. -/



section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (p : X) (hgeo : IsGeodesicSpace X) {τ : ℝ} (hτ : 0 < τ)
include hgeo hτ
 theorem coupling_of_compact_hopf_bound (A : ℝ)
    (hA : ∀ (φ : X → ℝ) (L : ℝ≥0), LipschitzWith L φ →
      ∀ R : ℝ, (∀x, R < dist p x → φ x = 0) →
      (∫x, hopfLax φ τ x ∂ν)-(∫x, φ x ∂μ) ≤ A) :
    ∃ π : Measure (X×X), IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧
      π.map Prod.snd = ν ∧ (∫⁻xy, ENNReal.ofReal (dist xy.1 xy.2^2/(2*τ)) ∂π) ≤ ENNReal.ofReal A := by
  let c : C(X×X,ℝ) := ⟨(fun xy : X×X => dist xy.1 xy.2^2/(2*τ)),
    ((continuous_fst.dist continuous_snd).pow 2).div_const _⟩
  apply BoundedTransport.coupling_of_dual_bound μ ν p p c (fun xy => by
    change 0 ≤ dist xy.1 xy.2^2/(2*τ); positivity) A
  intro u v huv
  let f : X →ᵇ ℝ := -(u+BoundedContinuousFunction.const X ‖u‖)
  let g : X →ᵇ ℝ := v-BoundedContinuousFunction.const X ‖u‖
  have hf (x : X) : f x ≤ 0 := by
    change -(u x+‖u‖) ≤ 0
    have hh := (abs_le.mp (u.norm_coe_le_norm x)).1
    linarith
  have hcontest (n : ℕ) : (∫x, g x ∂ν)-(∫x, compactUpperApprox p f n x ∂μ) ≤ A := by
    obtain ⟨L,hL⟩ := compactUpperApprox_lipschitz p hf n
    have hbound (x : X) : -‖f‖ ≤ compactUpperApprox p f n x :=
      ((abs_le.mp (f.norm_coe_le_norm x)).1).trans (compactUpperApprox_bounds p hf n x).1
    have hQ (x : X) : -‖f‖ ≤ hopfLax (compactUpperApprox p f n) τ x ∧
        hopfLax (compactUpperApprox p f n) τ x ≤ 0 := by
      refine ⟨le_csInf ⟨_,mem_range_self x⟩ ?_,
        (hopfLax_bounds hL hτ x).2.trans (compactUpperApprox_bounds p hf n x).2⟩
      rintro _ ⟨y,rfl⟩
      exact (hbound y).trans (le_add_of_nonneg_right (by positivity))
    have hQi : Integrable (hopfLax (compactUpperApprox p f n) τ) ν := by
      apply (integrable_const ‖f‖).mono'
        (hopfLax_lipschitz hL hgeo hτ).continuous.aestronglyMeasurable
      exact ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonpos (hQ x).2]
        linarith [(hQ x).1])
    have hgQ (x : X) : g x ≤ hopfLax (compactUpperApprox p f n) τ x := by
      obtain ⟨y,hy,_⟩ := hopfLax_exists_minimizer hL hτ x
      rw [hy]
      have hh := huv (y,x)
      change u y+v x ≤ dist y x^2/(2*τ) at hh
      have hfy := (compactUpperApprox_bounds p hf n y).1
      change -(u y+‖u‖) ≤ compactUpperApprox p f n y at hfy
      change v x-‖u‖ ≤ _
      rw [dist_comm y x] at hh
      linarith
    have hh := hA (compactUpperApprox p f n) L hL (2*((n:ℝ)+1)) (fun x hx => by
      dsimp only [compactUpperApprox]
      rw [radialCutoff_eq_zero p (by positivity) hx.le,zero_mul])
    linarith [integral_mono (g.integrable ν) hQi hgQ]
  have ht := (tendsto_const_nhds (x := ∫x, g x ∂ν)).sub (compactUpperApprox_integral_tendsto μ p f hf)
  have hlim : (∫x, g x ∂ν)-(∫x, f x ∂μ) ≤ A := le_of_tendsto ht (Eventually.of_forall hcontest)
  have hfI : (∫x, f x ∂μ) = -((∫x, u x ∂μ)+‖u‖) := by
    simp only [f,BoundedContinuousFunction.neg_apply,BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.const_apply,integral_neg,integral_add (u.integrable μ) (integrable_const _),
      integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
  have hgI : (∫x, g x ∂ν) = (∫x, v x ∂ν)-‖u‖ := by
    simp only [g,BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.const_apply,
      integral_sub (v.integrable ν) (integrable_const _),integral_const,measureReal_def,measure_univ,
      ENNReal.toReal_one,one_smul]
  rw [hfI,hgI] at hlim
  linarith
end RegularPointCoordinates
end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [ProperSpace X]
 theorem hopfLax_zero_outside {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (p : X) (R : ℝ) (hzero : ∀x, R < dist p x → f x = 0)
    {t : ℝ} (ht : 0 < t) {x : X} (hx : R+2*t*(L:ℝ) < dist p x) :
    hopfLax f t x = 0 := by
  obtain ⟨y,he,hd⟩ := hopfLax_exists_minimizer hf ht x
  have hy : R < dist p y := by linarith [dist_triangle p y x,dist_comm y x]
  have hfx : f x = 0 := hzero x (by linarith [mul_nonneg (by linarith : 0 ≤ 2*t) L.coe_nonneg])
  have hfy : f y = 0 := hzero y hy
  have hb := (hopfLax_bounds hf ht x).2
  rw [hfx] at hb
  rw [he,hfy,zero_add] at hb ⊢
  exact le_antisymm hb (div_nonneg (sq_nonneg _) (by positivity))

noncomputable def hopfPath (f : X → ℝ) (a b t : ℝ) (x : X) : ℝ :=
  hopfLax f (max a (min b t)) x
 theorem hopfPath_time_lipschitz {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hgeo : IsGeodesicSpace X) {a b : ℝ} (ha : 0 < a) (x : X) :
    LipschitzWith ⟨(L:ℝ)^2/2,by positivity⟩ (fun t => hopfPath f a b t x) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have h := hopfLax_time_difference_sharp hf hgeo
    (lt_of_lt_of_le ha (le_max_left _ _)) (lt_of_lt_of_le ha (le_max_left _ _)) x
    (s := max a (min b t)) (t := max a (min b s))
  have hc := ((LipschitzWith.id.const_min b).const_max a).dist_le_mul s t
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hc
  exact h.trans (mul_le_mul_of_nonneg_left hc (by positivity))
 theorem hopfPath_space_lipschitz {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hgeo : IsGeodesicSpace X) {a b : ℝ} (ha : 0 < a) (t : ℝ) :
    LipschitzWith L (hopfPath f a b t) :=
  hopfLax_lipschitz hf hgeo (lt_of_lt_of_le ha (le_max_left _ _))
 theorem hopfPath_joint_lipschitz {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hgeo : IsGeodesicSpace X) {a b : ℝ} (ha : 0 < a) :
    LipschitzWith (L+L^2/2)
      (fun q : X × ℝ => hopfPath f a b q.2 q.1) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  calc
    dist (hopfPath f a b v.2 v.1) (hopfPath f a b w.2 w.1) ≤
        dist (hopfPath f a b v.2 v.1) (hopfPath f a b v.2 w.1)+
        dist (hopfPath f a b v.2 w.1) (hopfPath f a b w.2 w.1) := dist_triangle _ _ _
    _ ≤ (L:ℝ)*dist v.1 w.1 + ((L:ℝ)^2/2)*dist v.2 w.2 := add_le_add
      ((hopfPath_space_lipschitz hf hgeo ha v.2).dist_le_mul _ _)
      ((hopfPath_time_lipschitz hf hgeo ha w.1).dist_le_mul _ _)
    _ ≤ (L:ℝ)*dist v w+((L:ℝ)^2/2)*dist v w := add_le_add
      (mul_le_mul_of_nonneg_left (show dist v.1 w.1 ≤ dist v w from le_max_left _ _) L.coe_nonneg)
      (mul_le_mul_of_nonneg_left (show dist v.2 w.2 ≤ dist v w from le_max_right _ _) (by positivity))
    _ = _ := by simp only [NNReal.coe_add,NNReal.coe_div,NNReal.coe_pow,NNReal.coe_ofNat]; ring
 theorem hopfPath_zero_outside {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (p : X) (R : ℝ) (hzero : ∀x, R < dist p x → f x = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {x : X}
    (hx : R+2*b*(L:ℝ) < dist p x) (t : ℝ) : hopfPath f a b t x = 0 := by
  apply hopfLax_zero_outside hf p R hzero (lt_of_lt_of_le ha (le_max_left _ _))
  have hb : max a (min b t) ≤ b := max_le hab (min_le_left _ _)
  have hm := mul_le_mul_of_nonneg_right hb L.coe_nonneg
  linarith
 theorem hopfPath_hasCompactSupport {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (p : X) (R : ℝ) (hzero : ∀x, R < dist p x → f x = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    HasCompactSupport (hopfPath f a b t) := by
  apply HasCompactSupport.intro (isCompact_closedBall p (R+2*b*(L:ℝ)))
  intro x hx
  apply hopfPath_zero_outside hf p R hzero ha hab _ t
  simpa only [mem_closedBall,not_le,dist_comm] using hx
omit [ProperSpace X] in
 theorem hopfPath_eq {f : X → ℝ} {a b t : ℝ} (ht : t ∈ Icc a b) :
    hopfPath f a b t = hopfLax f t := by
  funext x
  change hopfLax f (max a (min b t)) x = hopfLax f t x
  rw [min_eq_right ht.2,max_eq_right ht.1]
omit [ProperSpace X] in
 theorem hopfPath_eventuallyEq {f : X → ℝ} {a b t : ℝ} (ht : t ∈ Ioo a b) (x : X) :
    (fun s => hopfPath f a b s x) =ᶠ[𝓝 t] (fun s => hopfLax f s x) := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  rw [hopfPath_eq ⟨hs.1.le,hs.2.le⟩]
end RegularPointCoordinates
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
namespace L2Differentiation
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
 theorem integral_sq (f : Lp ℝ 2 μ) : (∫x, f x^2 ∂μ) = ‖f‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  congr 1
  funext x
  simp only [Real.inner_apply,pow_two]
 theorem toLp_tendsto_of_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → X → ℝ} {f : X → ℝ} (hF : ∀ i, MemLp (F i) 2 μ) (hf : MemLp f 2 μ)
    (B : X → ℝ) (hB : Integrable B μ)
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, (F i x-f x)^2 ≤ B x)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    Tendsto (fun i => (hF i).toLp (F i)) l (𝓝 (hf.toLp f)) := by
  have hi : Tendsto (fun i => ∫x, (F i x-f x)^2 ∂μ) l (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence B
      (F := fun i x => (F i x-f x)^2) (f := fun _ => (0:ℝ))
      (Eventually.of_forall fun i => ((hF i).aestronglyMeasurable.sub hf.aestronglyMeasurable).pow 2)
      (hb.mono fun i hi => hi.mono fun x hx => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (F i x-f x))] using hx) hB
      (ht.mono fun x hx => by simpa only [sub_self,zero_pow (by norm_num : 2 ≠ 0)] using
        (hx.sub (tendsto_const_nhds (x := f x))).pow 2)
    simpa only [integral_zero] using hh
  have he (i : ι) : (∫x, (F i x-f x)^2 ∂μ) = ‖(hF i).toLp (F i)-hf.toLp f‖^2 := by
    rw [← integral_sq]
    apply integral_congr_ae
    filter_upwards [(hF i).coeFn_toLp,hf.coeFn_toLp,Lp.coeFn_sub ((hF i).toLp (F i)) (hf.toLp f)] with x hx hy hz
    rw [hz]
    change (F i x-f x)^2 = (((hF i).toLp (F i)) x - (hf.toLp f) x)^2
    rw [hx,hy]
  simp only [he] at hi
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hi
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

 theorem toLp_hasDerivAt (F : ℝ → X → ℝ) (hF : ∀t, MemLp (F t) 2 μ)
    (D : X → ℝ) (hD : MemLp D 2 μ) (t : ℝ) (B : X → ℝ) (hB : Integrable B μ)
    (hb : ∀ᶠ s in 𝓝[≠] t, ∀ᵐ x ∂μ, ((s-t)⁻¹*(F s x-F t x)-D x)^2 ≤ B x)
    (hd : ∀ᵐ x ∂μ, HasDerivAt (fun s => F s x) (D x) t) :
    HasDerivAt (fun s => (hF s).toLp (F s)) (hD.toLp D) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hm (s : ℝ) : MemLp (fun x => (s-t)⁻¹*(F s x-F t x)) 2 μ :=
    ((hF s).sub (hF t)).const_mul _
  have hh := toLp_tendsto_of_dominated μ hm hD B hB hb
    (hd.mono fun x hx => hx.tendsto_slope)
  convert hh using 1
  funext s
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (s-t)⁻¹ ((hF s).toLp (F s)-(hF t).toLp (F t)),
    Lp.coeFn_sub ((hF s).toLp (F s)) ((hF t).toLp (F t)),
    (hF s).coeFn_toLp,(hF t).coeFn_toLp,(hm s).coeFn_toLp] with x hs hst hFs hFt hms
  change ((s-t)⁻¹ • ((hF s).toLp (F s)-(hF t).toLp (F t))) x = _
  rw [hs]
  change (s-t)⁻¹ * (((hF s).toLp (F s)-(hF t).toLp (F t)) x) = _
  rw [hst]
  change (s-t)⁻¹ * (((hF s).toLp (F s)) x-((hF t).toLp (F t)) x) = _
  rw [hFs,hFt,hms]
end L2Differentiation
end RegularPointCoordinates
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates.L2Differentiation
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [SFinite μ]
 theorem ae_fiber_differentiable (F : ℝ → X → ℝ)
    (hc : Continuous (fun p : X × ℝ => F p.2 p.1)) {C : ℝ≥0}
    (hl : ∀x, LipschitzWith C (fun t => F t x)) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ x ∂μ, DifferentiableAt ℝ (fun t => F t x) t := by
  apply (Measure.ae_ae_comm (measurableSet_of_differentiableAt_with_param ℝ (f := fun x t => F t x) hc)).mp
  exact Eventually.of_forall fun x => (hl x).ae_differentiableAt

 omit [SFinite μ] in
 theorem deriv_memLp (F : ℝ → X → ℝ)
    (hc : Continuous (fun p : X × ℝ => F p.2 p.1)) {C : ℝ≥0}
    (hl : ∀x, LipschitzWith C (fun t => F t x)) (s : Set X)
    (hs : MeasurableSet s) (hfin : μ s ≠ ∞)
    (hzero : ∀x ∉ s, ∀t, F t x = 0) (t : ℝ) :
    MemLp (fun x => deriv (fun t => F t x) t) 2 μ := by
  have hm : Measurable (fun x => deriv (fun t => F t x) t) :=
    (measurable_deriv_with_param (f := fun x t => F t x) hc).comp
      (measurable_id.prodMk (measurable_const (a := t)))
  apply (memLp_indicator_const 2 hs (C:ℝ) (Or.inr hfin)).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  by_cases hx : x ∈ s
  · simpa only [indicator_of_mem hx] using norm_deriv_le_of_lipschitz (hl x)
  · have he : (fun t => F t x) = fun _ => (0:ℝ) := funext (hzero x hx)
    simp only [he,deriv_const,norm_zero,indicator_of_notMem hx,le_refl]

 omit [SFinite μ] [TopologicalSpace X] [BorelSpace X] in
 theorem toLp_lipschitz (F : ℝ → X → ℝ) (hF : ∀t, MemLp (F t) 2 μ)
    {C : ℝ≥0} (hl : ∀x, LipschitzWith C (fun t => F t x)) (s : Set X)
    (hs : MeasurableSet s) (hfin : μ s ≠ ∞)
    (hzero : ∀x ∉ s, ∀t, F t x = 0) :
    ∃ D : ℝ≥0, LipschitzWith D (fun t => (hF t).toLp (F t)) := by
  let hI := memLp_indicator_const (μ := μ) 2 hs (1:ℝ) (Or.inr hfin)
  let I := hI.toLp (s.indicator fun _ => (1:ℝ))
  refine ⟨C*‖I‖₊, LipschitzWith.of_dist_le_mul fun r t => ?_⟩
  rw [dist_eq_norm]
  have hn : ‖(hF r).toLp (F r)-(hF t).toLp (F t)‖ ≤ ((C:ℝ)*dist r t)*‖I‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(hF r).coeFn_toLp,(hF t).coeFn_toLp,hI.coeFn_toLp,
      Lp.coeFn_sub ((hF r).toLp (F r)) ((hF t).toLp (F t))] with x hr ht hi hsub
    rw [hsub]
    change ‖((hF r).toLp (F r)) x-((hF t).toLp (F t)) x‖ ≤ _
    rw [hr,ht]
    change ‖F r x-F t x‖ ≤ (C:ℝ)*dist r t*‖I x‖
    change _ ≤ (C:ℝ)*dist r t*‖hI.toLp (s.indicator fun _ => (1:ℝ)) x‖
    rw [hi]
    by_cases hx : x ∈ s
    · simpa only [indicator_of_mem hx,norm_one,mul_one,← dist_eq_norm] using
        (hl x).dist_le_mul r t
    · simp only [hzero x hx r,hzero x hx t,sub_self,norm_zero,indicator_of_notMem hx,
        norm_zero,mul_zero,le_refl]
  simpa only [NNReal.coe_mul,coe_nnnorm,mul_right_comm] using hn

 theorem ae_toLp_hasDerivAt (F : ℝ → X → ℝ) (hF : ∀t, MemLp (F t) 2 μ)
    (hc : Continuous (fun p : X × ℝ => F p.2 p.1)) {C : ℝ≥0}
    (hl : ∀x, LipschitzWith C (fun t => F t x)) (s : Set X)
    (hs : MeasurableSet s) (hfin : μ s ≠ ∞)
    (hzero : ∀x ∉ s, ∀t, F t x = 0) :
    ∀ᵐ t ∂(volume : Measure ℝ), HasDerivAt (fun t => (hF t).toLp (F t))
      ((deriv_memLp μ F hc hl s hs hfin hzero t).toLp (fun x => deriv (fun t => F t x) t)) t := by
  filter_upwards [ae_fiber_differentiable μ F hc hl] with t ht
  apply toLp_hasDerivAt μ F hF _ _ t (s.indicator fun _ => (2*(C:ℝ))^2)
  · exact (integrableOn_const (C := (2*(C:ℝ))^2) hfin).integrable_indicator hs
  · apply Eventually.of_forall
    intro r
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx]
      have hD := norm_deriv_le_of_lipschitz (hl x) (x₀ := t)
      have hdiff := (hl x).dist_le_mul r t
      have hquot : |(r-t)⁻¹ * (F r x-F t x)| ≤ C := by
        rcases eq_or_ne r t with rfl | hne
        · simp
        · rw [abs_mul,abs_inv,← div_eq_inv_mul]
          apply (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hne))).mpr
          simpa only [Real.dist_eq] using hdiff
      have hnorm := abs_sub_le ((r-t)⁻¹ * (F r x-F t x)) 0 (deriv (fun t => F t x) t)
      have hbound : |(r-t)⁻¹ * (F r x-F t x)-deriv (fun t => F t x) t| ≤ 2*(C:ℝ) := by
        simpa only [sub_zero,zero_sub,abs_neg] using hnorm.trans (by
          simpa only [Real.norm_eq_abs,two_mul,sub_zero,zero_sub,abs_neg] using add_le_add hquot hD)
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hbound 2
      simpa only [sq_abs] using hsq
    · have he : (fun t => F t x) = fun _ => (0:ℝ) := funext (hzero x hx)
      simp only [hzero x hx r,hzero x hx t,he,deriv_const,sub_zero,mul_zero,zero_pow
        (by norm_num : 2 ≠ 0),indicator_of_notMem hx,le_refl]
  · exact ht.mono fun x hx => hx.hasDerivAt
end RegularPointCoordinates.L2Differentiation
end

 
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)
 theorem SobolevSpace.ofLipschitzCompact_minimalSlope_le_slope {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (SobolevSpace.ofLipschitzCompact μ hQ hf hs) x ≤
      (localSlope f x).toReal := by
  have he := (slopeEnergy_lt_top_of_lipschitz_hasCompactSupport μ hf hs).ne
  have hG : IsSlopeMajorant μ f (lipschitzSlopeLp μ hf he) := by
    filter_upwards [lipschitzSlopeLp_nonneg μ hf he,lipschitzSlopeLp_enorm μ hf he] with x hn hx
    rw [Real.enorm_of_nonneg hn] at hx
    exact ⟨hn,hx.ge⟩
  have hle := (Lp.coeFn_le _ _).mpr (SobolevSpace.ofLipschitzCompact_minimalSlope_le μ hQ hf hs hG)
  filter_upwards [hle,(localSlope_toReal_memLp μ hf he).coeFn_toLp] with x hx hy
  exact hx.trans_eq hy
 theorem SobolevSpace.ofLipschitzCompact_minimalSlope_le_lip {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (SobolevSpace.ofLipschitzCompact μ hQ hf hs) x ≤ L := by
  filter_upwards [SobolevSpace.ofLipschitzCompact_minimalSlope_le_slope μ hQ hf hs] with x hx
  exact hx.trans (by
    have h := localSlope_le_of_lipschitz hf x
    have hh := ENNReal.toReal_mono ENNReal.coe_ne_top h
    simpa only [ENNReal.coe_toReal] using hh)

variable {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hgeo : IsGeodesicSpace X)
  (p : X) (R : ℝ) (hzero : ∀x, R < dist p x → f x = 0)
  {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
include hQ
noncomputable def hopfPathSobolev (t : ℝ) : SobolevSpace μ hQ :=
  SobolevSpace.ofLipschitzCompact μ hQ (hopfPath_space_lipschitz hf hgeo ha t)
    (hopfPath_hasCompactSupport hf p R hzero ha hab t)
 theorem hopfPathSobolev_coe (t : ℝ) :
    ⇑(SobolevSpace.toLp μ hQ (hopfPathSobolev μ hQ hf hgeo p R hzero ha hab t)) =ᵐ[μ]
      hopfPath f a b t := SobolevSpace.ofLipschitzCompact_coe μ hQ _ _
 theorem hopfPathSobolev_lipschitz : ∃ C : ℝ≥0,
    LipschitzWith C (fun t => SobolevSpace.toLp μ hQ
      (hopfPathSobolev μ hQ hf hgeo p R hzero ha hab t)) := by
  apply L2Differentiation.toLp_lipschitz μ (hopfPath f a b)
    (fun t => (hopfPath_space_lipschitz hf hgeo ha t).continuous.memLp_of_hasCompactSupport
      (hopfPath_hasCompactSupport hf p R hzero ha hab t))
    (hopfPath_time_lipschitz hf hgeo ha) (closedBall p (R+2*b*(L:ℝ)))
    measurableSet_closedBall ((isCompact_closedBall _ _).measure_lt_top.ne)
  intro x hx t
  exact hopfPath_zero_outside hf p R hzero ha hab
    (by simpa only [mem_closedBall,not_le,dist_comm] using hx) t

variable [SigmaFinite μ]
 theorem hopfPathSobolev_ae_hasDerivAt_hj :
    ∀ᵐ t ∂(volume : Measure ℝ), ∃ D : Lp ℝ 2 μ,
      HasDerivAt (fun s => SobolevSpace.toLp μ hQ
        (hopfPathSobolev μ hQ hf hgeo p R hzero ha hab s)) D t ∧
      (t ∈ Ioo a b → ∀ᵐ x ∂μ, D x +
        SobolevSpace.minimalSlope μ hQ (hopfPathSobolev μ hQ hf hgeo p R hzero ha hab t) x^2/2 ≤ 0) := by
  let F := hopfPath f a b
  let hF (t : ℝ) : MemLp (F t) 2 μ :=
    (hopfPath_space_lipschitz hf hgeo ha t).continuous.memLp_of_hasCompactSupport
      (hopfPath_hasCompactSupport hf p R hzero ha hab t)
  have hc : Continuous (fun q : X × ℝ => F q.2 q.1) :=
    (hopfPath_joint_lipschitz hf hgeo ha).continuous
  have hl := hopfPath_time_lipschitz hf hgeo ha (b := b)
  let S := closedBall p (R+2*b*(L:ℝ))
  have hS : MeasurableSet S := measurableSet_closedBall
  have hSf : μ S ≠ ∞ := (isCompact_closedBall _ _).measure_lt_top.ne
  have h0 : ∀x ∉ S, ∀t, F t x = 0 := by
    intro x hx t
    exact hopfPath_zero_outside hf p R hzero ha hab
      (by simpa only [S,mem_closedBall,not_le,dist_comm] using hx) t
  have hd := L2Differentiation.ae_toLp_hasDerivAt μ F hF hc hl S hS hSf h0
  have hpt := L2Differentiation.ae_fiber_differentiable μ F hc hl
  filter_upwards [hd,hpt] with t ht hpt
  let hD := L2Differentiation.deriv_memLp μ F hc hl S hS hSf h0 t
  refine ⟨hD.toLp _,ht,fun ht => ?_⟩
  have hG := SobolevSpace.ofLipschitzCompact_minimalSlope_le_slope μ hQ
    (hopfPath_space_lipschitz hf hgeo ha t) (hopfPath_hasCompactSupport hf p R hzero ha hab t)
  have hn := (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ
    (hopfPathSobolev μ hQ hf hgeo p R hzero ha hab t))
  filter_upwards [hD.coeFn_toLp,hG,hn,hpt] with x hDx hGx hnx hptx
  rw [hDx]
  have hdr : HasDerivAt (fun s => hopfLax f s x) (deriv (fun s => F s x) t) t :=
    hptx.hasDerivAt.congr_of_eventuallyEq (hopfPath_eventuallyEq ht x).symm
  have hh := hopfLax_hamiltonJacobi hf (ha.trans ht.1) x hdr
  have he : F t = hopfLax f t := hopfPath_eq ⟨ht.1.le,ht.2.le⟩
  change _ ≤ (localSlope (F t) x).toReal at hGx
  rw [he] at hGx
  have hsq := pow_le_pow_left₀ hnx hGx 2
  dsimp only [F] at hh
  linarith
end RegularPointCoordinates

end OAI
