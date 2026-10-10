import Mathlib
import OAI.Probability.IsingPerceptron.NormalizedRestrictionPi

namespace OAI

/-! Convex Derivative Fluctuation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma convex_derivative_fluctuation {f g : ℝ → ℝ} {v s df dg C : ℝ}
    (hs : 0 < s) (hc : ConvexOn ℝ (Icc (v-s) (v+s)) f)
    (hd : HasDerivAt f df v)
    (hplus : g (v+s) - g v - s * dg ≤ C * s^2)
    (hminus : g (v-s) - g v + s * dg ≤ C * s^2) :
    |df-dg| ≤ C*s +
      (|f (v+s)-g (v+s)| + |f (v-s)-g (v-s)| + 2*|f v-g v|)/s := by
  have hv : v ∈ Icc (v-s) (v+s) := ⟨by linarith, by linarith⟩
  have hl := hc.slope_le_of_hasDerivAt (show v-s ∈ Icc (v-s) (v+s) from
    ⟨le_rfl, by linarith⟩) hv (by linarith : v-s < v) hd
  have hr := hc.le_slope_of_hasDerivAt hv (show v+s ∈ Icc (v-s) (v+s) from
    ⟨by linarith, le_rfl⟩) (by linarith : v < v+s) hd
  rw [slope_def_field] at hl hr
  have hl' : f v - f (v-s) ≤ df*s := by
    have := (div_le_iff₀ (show 0 < v-(v-s) by linarith)).mp hl
    nlinarith
  have hr' : df*s ≤ f (v+s)-f v := by
    have := (le_div_iff₀ (show 0 < v+s-v by linarith)).mp hr
    nlinarith
  rw [abs_le]
  constructor
  · apply (mul_le_mul_iff_of_pos_right hs).mp
    simp only [neg_mul, add_mul, div_mul_cancel₀ _ hs.ne']
    nlinarith [le_abs_self (f (v-s)-g (v-s)), neg_abs_le (f v-g v),
      abs_nonneg (f (v+s)-g (v+s)), abs_nonneg (f v-g v)]
  · apply (mul_le_mul_iff_of_pos_right hs).mp
    simp only [add_mul, div_mul_cancel₀ _ hs.ne']
    nlinarith [le_abs_self (f (v+s)-g (v+s)), neg_abs_le (f v-g v),
      abs_nonneg (f (v-s)-g (v-s)), abs_nonneg (f v-g v)]

lemma minimizer_quadratic_remainder {g : ℝ → ℝ} {v c a dg x : ℝ}
    (hmin : -g v + c*(v-a)^2 ≤ -g x + c*(x-a)^2)
    (hstationary : dg = 2*c*(v-a)) :
    g x - g v - (x-v)*dg ≤ c*(x-v)^2 := by
  rw [hstationary]
  nlinarith

lemma integral_convex_derivative_fluctuation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ → ℝ} {g : ℝ → ℝ}
    {v s dg C δ : ℝ} {df : Ω → ℝ} (hs : 0 < s)
    (hc : ∀ ω, ConvexOn ℝ (Icc (v-s) (v+s)) (f ω))
    (hd : ∀ ω, HasDerivAt (f ω) (df ω) v)
    (hplus : g (v+s)-g v-s*dg ≤ C*s^2)
    (hminus : g (v-s)-g v+s*dg ≤ C*s^2)
    (hfplus : Integrable (fun ω => f ω (v+s)) μ)
    (hfminus : Integrable (fun ω => f ω (v-s)) μ)
    (hfv : Integrable (fun ω => f ω v) μ)
    (hm : AEStronglyMeasurable df μ)
    (hep : (∫ ω, |f ω (v+s)-g (v+s)| ∂μ) ≤ δ)
    (hem : (∫ ω, |f ω (v-s)-g (v-s)| ∂μ) ≤ δ)
    (hev : (∫ ω, |f ω v-g v| ∂μ) ≤ δ) :
    (∫ ω, |df ω-dg| ∂μ) ≤ C*s+4*δ/s := by
  have hp : Integrable (fun ω => |f ω (v+s)-g (v+s)|) μ := (hfplus.sub (integrable_const (g (v+s)))).abs
  have hn : Integrable (fun ω => |f ω (v-s)-g (v-s)|) μ := (hfminus.sub (integrable_const (g (v-s)))).abs
  have hv : Integrable (fun ω => |f ω v-g v|) μ := (hfv.sub (integrable_const (g v))).abs
  have hi : Integrable (fun ω => C*s+(|f ω (v+s)-g (v+s)|+
      |f ω (v-s)-g (v-s)|+2*|f ω v-g v|)/s) μ :=
    (integrable_const (C*s)).add ((hp.add hn |>.add (hv.const_mul 2)).div_const s)
  have hib : Integrable (fun ω => (|f ω (v+s)-g (v+s)|+
      |f ω (v-s)-g (v-s)|+2*|f ω v-g v|)/s) μ :=
    (hp.add hn |>.add (hv.const_mul 2)).div_const s
  have hic : Integrable (fun ω => |f ω (v+s)-g (v+s)|+|f ω (v-s)-g (v-s)|) μ := hp.add hn
  have hie : Integrable (fun ω => 2*|f ω v-g v|) μ := hv.const_mul 2
  have hb ω := convex_derivative_fluctuation hs (hc ω) (hd ω) hplus hminus
  have hid : Integrable (fun ω => |df ω-dg|) μ := hi.mono'
    ((hm.sub aestronglyMeasurable_const).norm) (ae_of_all μ (fun ω => by
      simpa only [Real.norm_eq_abs, abs_abs] using hb ω))
  calc
    _ ≤ ∫ ω, C*s+(|f ω (v+s)-g (v+s)|+|f ω (v-s)-g (v-s)|+
        2*|f ω v-g v|)/s ∂μ := integral_mono hid hi hb
    _ = C*s+((∫ ω, |f ω (v+s)-g (v+s)| ∂μ)+
        (∫ ω, |f ω (v-s)-g (v-s)| ∂μ)+2*(∫ ω, |f ω v-g v| ∂μ))/s := by
      rw [integral_add (integrable_const _) hib,
        integral_div, integral_add hic hie, integral_add hp hn,
        integral_const_mul]
      simp [integral_const_mul]
    _ ≤ C*s+4*δ/s := by gcongr; linarith

lemma localMin_second_derivative_nonneg {f : ℝ → ℝ} {v : ℝ}
    (hmin : IsLocalMin f v) (hc : ContinuousAt f v) :
    0 ≤ deriv (deriv f) v := by
  by_contra h
  have hmax := isLocalMax_of_deriv_deriv_neg (lt_of_not_ge h) hmin.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 v] fun _ => f v := by
    filter_upwards [hmin,hmax] with x hx hy
    exact le_antisymm hy hx
  have hd : deriv (deriv f) v = 0 := by simpa using he.deriv.deriv_eq
  exact h (le_of_eq hd.symm)

lemma localMin_quadratic_stationary {g dg : ℝ → ℝ} {v c a : ℝ}
    (hmin : IsLocalMin (fun x => -g x+c*(x-a)^2) v)
    (hd : HasDerivAt g (dg v) v) : dg v = 2*c*(v-a) := by
  have hp : HasDerivAt (fun x : ℝ => -g x+c*(x-a)^2)
      (-dg v+c*(2*(v-a))) v := by
    convert hd.neg.add ((((hasDerivAt_id v).sub_const a).pow 2).const_mul c) using 1 <;> try rfl
    simp
  have he := hmin.hasDerivAt_eq_zero hp
  linarith

lemma localMin_quadratic_curvature {g dg : ℝ → ℝ} {v c a ddg : ℝ}
    (hmin : IsLocalMin (fun x => -g x+c*(x-a)^2) v)
    (hd : ∀ x, HasDerivAt g (dg x) x) (hdd : HasDerivAt dg ddg v) : ddg ≤ 2*c := by
  let F := fun x => -g x+c*(x-a)^2
  have hF (x : ℝ) : HasDerivAt F (-dg x+c*(2*(x-a))) x := by
    dsimp only [F]
    convert (hd x).neg.add ((((hasDerivAt_id x).sub_const a).pow 2).const_mul c) using 1 <;> try rfl
    simp
  have he : deriv F = fun x => -dg x+c*(2*(x-a)) := funext (fun x => (hF x).deriv)
  have hdF : HasDerivAt (deriv F) (-ddg+2*c) v := by
    rw [he]
    convert hdd.neg.add ((((hasDerivAt_id v).sub_const a).const_mul 2).const_mul c) using 1 <;> try rfl
    simp [mul_comm c 2]
  have hh := localMin_second_derivative_nonneg hmin (hF v).continuousAt
  rw [hdF.deriv] at hh
  linarith

theorem quadratic_minimizer_conditions {g dg : ℝ → ℝ} {v c a ddg : ℝ}
    (hmin : IsLocalMin (fun x => -g x+c*(x-a)^2) v)
    (hd : ∀ x, HasDerivAt g (dg x) x) (hdd : HasDerivAt dg ddg v) :
    dg v = 2*c*(v-a) ∧ ddg ≤ 2*c :=
  ⟨localMin_quadratic_stationary hmin (hd v), localMin_quadratic_curvature hmin hd hdd⟩

open ProbabilityTheory Filter

lemma tendsto_central_second_difference {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (v : ℝ) :
    Tendsto (fun h : ℝ => (f (v+h)+f (v-h)-2*f v)/h^2)
      (𝓝[≠] 0) (𝓝 (iteratedDeriv 2 f v)) := by
  have ht := Real.taylor_tendsto (x₀ := v) (n := 2) convex_univ (mem_univ v) hf.contDiffOn
  simp only [nhdsWithin_univ] at ht
  have ht' : Tendsto (fun x => (f x-(f v+(x-v)*deriv f v+
      (x-v)^2/2*iteratedDeriv 2 f v))/(x-v)^2) (𝓝 v) (𝓝 0) := by
    convert ht using 1
    ext x
    simp [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ,
      iteratedDeriv_one, smul_eq_mul]
    ring
  have hid : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hp := ht'.comp (show Tendsto (fun h : ℝ => v+h) (𝓝[≠] 0) (𝓝 v) by simpa using hid.const_add v)
  have hn := ht'.comp (show Tendsto (fun h : ℝ => v-h) (𝓝[≠] 0) (𝓝 v) by simpa using hid.const_sub v)
  have he : (fun h : ℝ => (f (v+h)+f (v-h)-2*f v)/h^2) =ᶠ[𝓝[≠] 0]
      (fun h => ((f (v+h)-(f v+(v+h-v)*deriv f v+
        (v+h-v)^2/2*iteratedDeriv 2 f v))/(v+h-v)^2)+
        ((f (v-h)-(f v+(v-h-v)*deriv f v+
        (v-h-v)^2/2*iteratedDeriv 2 f v))/(v-h-v)^2)+iteratedDeriv 2 f v) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : h ≠ 0 := hh
    field_simp [hh']
    ring
  simpa only [zero_add] using ((hp.add hn).add_const (iteratedDeriv 2 f v)).congr' he.symm

lemma integrable_limit_of_integral_bound {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {F : ι → Ω → ℝ} {g : Ω → ℝ} {C : ℝ}
    (hi : ∀ i, Integrable (F i) μ) (hnn : ∀ i ω, 0 ≤ F i ω)
    (hb : ∀ᶠ i in l, (∫ ω, F i ω ∂μ) ≤ C)
    (hl : ∀ ω, Tendsto (fun i => F i ω) l (𝓝 (g ω))) :
    Integrable g μ ∧ (∫ ω, g ω ∂μ) ≤ C := by
  have hgn (ω : Ω) : 0 ≤ g ω := ge_of_tendsto (hl ω) (Eventually.of_forall (fun i => hnn i ω))
  have hgm : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae l
    (fun i => (hi i).aestronglyMeasurable) (ae_of_all _ hl)
  have hC : 0 ≤ C := by
    obtain ⟨i, h⟩ := hb.exists
    exact (integral_nonneg (hnn i)).trans h
  have he : (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ ω, liminf (fun i => ENNReal.ofReal (F i ω)) l ∂μ := by
        apply lintegral_congr
        intro ω
        exact (ENNReal.tendsto_ofReal (hl ω)).liminf_eq.symm
      _ ≤ liminf (fun i => ∫⁻ ω, ENNReal.ofReal (F i ω) ∂μ) l :=
        lintegral_liminf_le' (fun i => (hi i).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ _ := by
        refine liminf_le_of_frequently_le ?_ (isBoundedUnder_of ⟨0, fun _ => zero_le⟩)
        apply Eventually.frequently
        filter_upwards [hb] with i hiC
        rw [← ofReal_integral_eq_lintegral_ofReal (hi i) (ae_of_all _ (hnn i))]
        exact ENNReal.ofReal_le_ofReal hiC
  have hgi : Integrable g μ := (lintegral_ofReal_ne_top_iff_integrable hgm (ae_of_all _ hgn)).mp
    (ne_of_lt (he.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hgi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hgn) hgm]
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top he

lemma central_second_difference_nonneg {f : ℝ → ℝ}
    (hc : ConvexOn ℝ univ f) (v h : ℝ) : 0 ≤ (f (v+h)+f (v-h)-2*f v)/h^2 := by
  have he := hc.2 (mem_univ (v+h)) (mem_univ (v-h))
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have hav : (1/2:ℝ) • (v+h)+(1/2:ℝ) • (v-h) = v := by simp only [smul_eq_mul]; ring
  rw [hav] at he
  simp only [smul_eq_mul] at he
  exact div_nonneg (by linarith) (sq_nonneg h)

theorem expected_curvature_at_minimum {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ → ℝ} {v c a : ℝ}
    (hc : ∀ ω, ConvexOn ℝ univ (f ω)) (hd : ∀ ω, ContDiff ℝ 2 (f ω))
    (hi : ∀ t, Integrable (fun ω => f ω t) μ)
    (hmin : IsLocalMin (fun t => -(∫ ω, f ω t ∂μ)+c*(t-a)^2) v) :
    Integrable (fun ω => iteratedDeriv 2 (f ω) v) μ ∧
      (∫ ω, iteratedDeriv 2 (f ω) v ∂μ) ≤ 2*c := by
  let F := fun h ω => (f ω (v+h)+f ω (v-h)-2*f ω v)/h^2
  have hF (h : ℝ) : Integrable (F h) μ := ((hi (v+h)).add (hi (v-h)) |>.sub
    ((hi v).const_mul 2)).div_const _
  have hid : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hp : ∀ᶠ h in 𝓝[≠] (0:ℝ),
      -(∫ ω, f ω v ∂μ)+c*(v-a)^2 ≤ -(∫ ω, f ω (v+h) ∂μ)+c*(v+h-a)^2 :=
    (show Tendsto (fun h : ℝ => v+h) (𝓝[≠] 0) (𝓝 v) by simpa using hid.const_add v).eventually hmin
  have hn : ∀ᶠ h in 𝓝[≠] (0:ℝ),
      -(∫ ω, f ω v ∂μ)+c*(v-a)^2 ≤ -(∫ ω, f ω (v-h) ∂μ)+c*(v-h-a)^2 :=
    (show Tendsto (fun h : ℝ => v-h) (𝓝[≠] 0) (𝓝 v) by simpa using hid.const_sub v).eventually hmin
  apply integrable_limit_of_integral_bound (l := 𝓝[≠] (0:ℝ)) hF
    (fun h ω => central_second_difference_nonneg (hc ω) v h) ?_
    (fun ω => tendsto_central_second_difference (hd ω) v)
  filter_upwards [hp, hn, self_mem_nhdsWithin] with h hp' hn' hz
  dsimp only [F]
  rw [integral_div, integral_sub (f := fun ω => f ω (v+h)+f ω (v-h))
    (g := fun ω => 2*f ω v) ((hi (v+h)).add (hi (v-h))) ((hi v).const_mul 2),
    integral_add (hi (v+h)) (hi (v-h)), integral_const_mul]
  apply (div_le_iff₀ (sq_pos_of_ne_zero (show h ≠ 0 from hz))).mpr
  nlinarith

lemma mem_interior_integrableExpSet_of_all {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {Y : X → ℝ} (he : ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y x)) ν)
    (t : ℝ) : t ∈ interior (integrableExpSet Y ν) := by
  have h : integrableExpSet Y ν = univ := Set.eq_univ_of_forall he
  simp [h]

lemma contDiff_cgf_of_all_exp {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {Y : X → ℝ} (he : ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y x)) ν) :
    ContDiff ℝ 2 (cgf Y ν) :=
  contDiff_iff_contDiffAt.mpr (fun t =>
    (analyticAt_cgf (mem_interior_integrableExpSet_of_all he t)).contDiffAt)

lemma convexOn_cgf_of_all_exp {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {Y : X → ℝ} (he : ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y x)) ν) :
    ConvexOn ℝ univ (cgf Y ν) := by
  have hd := contDiff_cgf_of_all_exp he
  apply convexOn_univ_of_deriv2_nonneg (hd.differentiable (by norm_num)) hd.differentiable_deriv_two
  intro t
  have hv := variance_nonneg Y (ν.tilted (t*Y ·))
  rw [variance_tilted_mul (mem_interior_integrableExpSet_of_all he t)] at hv
  simpa [iteratedDeriv_succ, iteratedDeriv_zero, Function.iterate_succ_apply'] using hv

theorem expected_tilted_variance_at_minimum {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} (ν : Ω → Measure X) (Y : Ω → X → ℝ) {v c a : ℝ}
    (he : ∀ ω t, Integrable (fun x => Real.exp (t*Y ω x)) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (Y ω) (ν ω) t) μ)
    (hmin : IsLocalMin (fun t => -(∫ ω, cgf (Y ω) (ν ω) t ∂μ)+c*(t-a)^2) v) :
    Integrable (fun ω => Var[Y ω; (ν ω).tilted (v*Y ω ·)]) μ ∧
      (∫ ω, Var[Y ω; (ν ω).tilted (v*Y ω ·)] ∂μ) ≤ 2*c := by
  have ht := expected_curvature_at_minimum (fun ω => convexOn_cgf_of_all_exp (he ω))
    (fun ω => contDiff_cgf_of_all_exp (he ω)) hi hmin
  simpa only [variance_tilted_mul (mem_interior_integrableExpSet_of_all (he _) v)] using ht

lemma probability_thermal_young {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {Y : X → ℝ} (hY : MemLp Y 2 ν)
    {K : ℝ} (hK : 0 < K) :
    (∫ x, |Y x-(∫ y, Y y ∂ν)| ∂ν) ≤ (Var[Y; ν]+K^2)/(2*K) := by
  let m := ∫ y, Y y ∂ν
  have hi : Integrable (fun x => |Y x-m|) ν := ((hY.integrable (by norm_num)).sub (integrable_const m)).abs
  have hs : Integrable (fun x => (Y x-m)^2) ν := (hY.sub (memLp_const m)).integrable_sq
  calc
    _ ≤ ∫ x, ((Y x-m)^2+K^2)/(2*K) ∂ν := by
      apply integral_mono hi ((hs.add (integrable_const _)).div_const _)
      intro x
      change |Y x-m| ≤ ((Y x-m)^2+K^2)/(2*K)
      apply (le_div_iff₀ (by positivity : 0 < 2*K)).mpr
      nlinarith [sq_nonneg (|Y x-m|-K), sq_abs (Y x-m)]
    _ = _ := by
      rw [integral_div, integral_add hs (integrable_const _), integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rw [variance_eq_integral hY.aemeasurable]

end IsingPerceptron

namespace IsingPerceptron

theorem expected_curvature_at_minimum_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ → ℝ} {v c a : ℝ}
    (hc : ∀ᵐ ω ∂μ, ConvexOn ℝ univ (f ω))
    (hd : ∀ᵐ ω ∂μ, ContDiff ℝ 2 (f ω))
    (hi : ∀ t, Integrable (fun ω => f ω t) μ)
    (hmin : IsLocalMin (fun t => -(∫ ω, f ω t ∂μ)+c*(t-a)^2) v) :
    Integrable (fun ω => iteratedDeriv 2 (f ω) v) μ ∧
      (∫ ω, iteratedDeriv 2 (f ω) v ∂μ) ≤ 2*c := by
  classical
  let f' : Ω → ℝ → ℝ := fun ω =>
    if ConvexOn ℝ univ (f ω) ∧ ContDiff ℝ 2 (f ω) then f ω else fun _ => 0
  have he : ∀ᵐ ω ∂μ, f' ω = f ω := by
    filter_upwards [hc,hd] with ω hω hω'
    simp [f',hω,hω']
  have hc' (ω) : ConvexOn ℝ univ (f' ω) := by
    dsimp only [f']
    split_ifs with h
    · exact h.1
    · exact convexOn_const _ (convex_univ)   
  have hd' (ω) : ContDiff ℝ 2 (f' ω) := by
    dsimp only [f']
    split_ifs with h
    · exact h.2
    · exact contDiff_const
  have hi' (t) : Integrable (fun ω => f' ω t) μ :=
    (hi t).congr (he.mono fun _ h => congrFun h.symm t)
  have heI (t) : (∫ ω, f' ω t ∂μ) = ∫ ω, f ω t ∂μ :=
    integral_congr_ae (he.mono fun _ h => congrFun h t)
  have hmin' : IsLocalMin (fun t => -(∫ ω, f' ω t ∂μ)+c*(t-a)^2) v := by
    simpa only [heI] using hmin
  obtain ⟨h1,h2⟩ := expected_curvature_at_minimum hc' hd' hi' hmin'
  have hed : (fun ω => iteratedDeriv 2 (f' ω) v) =ᵐ[μ]
      (fun ω => iteratedDeriv 2 (f ω) v) := he.mono fun _ h => congrArg (fun k => iteratedDeriv 2 k v) h
  exact ⟨h1.congr hed,(integral_congr_ae hed).symm ▸ h2⟩

theorem expected_tilted_variance_at_minimum_ae {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {μ : Measure Ω}
    (ν : Ω → Measure X) (Y : Ω → X → ℝ) {v c a : ℝ}
    (he : ∀ᵐ ω ∂μ, ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y ω x)) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (Y ω) (ν ω) t) μ)
    (hmin : IsLocalMin (fun t => -(∫ ω, cgf (Y ω) (ν ω) t ∂μ)+c*(t-a)^2) v) :
    Integrable (fun ω => Var[Y ω; (ν ω).tilted (v*Y ω ·)]) μ ∧
      (∫ ω, Var[Y ω; (ν ω).tilted (v*Y ω ·)] ∂μ) ≤ 2*c := by
  obtain ⟨h1,h2⟩ := expected_curvature_at_minimum_ae
    (he.mono fun _ h => convexOn_cgf_of_all_exp h)
    (he.mono fun _ h => contDiff_cgf_of_all_exp h) hi hmin
  have hed : (fun ω => iteratedDeriv 2 (cgf (Y ω) (ν ω)) v) =ᵐ[μ]
      (fun ω => Var[Y ω; (ν ω).tilted (v*Y ω ·)]) := by
    filter_upwards [he] with ω hω
    exact (variance_tilted_mul (mem_interior_integrableExpSet_of_all hω v)).symm
  exact ⟨h1.congr hed,(integral_congr_ae hed).symm ▸ h2⟩

theorem integral_convex_derivative_fluctuation_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ → ℝ} {g : ℝ → ℝ}
    {v s dg C δ : ℝ} {df : Ω → ℝ} (hs : 0 < s)
    (hc : ∀ᵐ ω ∂μ, ConvexOn ℝ (Icc (v-s) (v+s)) (f ω))
    (hd : ∀ᵐ ω ∂μ, HasDerivAt (f ω) (df ω) v)
    (hplus : g (v+s)-g v-s*dg ≤ C*s^2)
    (hminus : g (v-s)-g v+s*dg ≤ C*s^2)
    (hfplus : Integrable (fun ω => f ω (v+s)) μ)
    (hfminus : Integrable (fun ω => f ω (v-s)) μ)
    (hfv : Integrable (fun ω => f ω v) μ)
    (hm : AEStronglyMeasurable df μ)
    (hep : (∫ ω, |f ω (v+s)-g (v+s)| ∂μ) ≤ δ)
    (hem : (∫ ω, |f ω (v-s)-g (v-s)| ∂μ) ≤ δ)
    (hev : (∫ ω, |f ω v-g v| ∂μ) ≤ δ) :
    Integrable df μ ∧ (∫ ω, |df ω-dg| ∂μ) ≤ C*s+4*δ/s := by
  have hp : Integrable (fun ω => |f ω (v+s)-g (v+s)|) μ := (hfplus.sub (integrable_const (g (v+s)))).abs
  have hn : Integrable (fun ω => |f ω (v-s)-g (v-s)|) μ := (hfminus.sub (integrable_const (g (v-s)))).abs
  have hv : Integrable (fun ω => |f ω v-g v|) μ := (hfv.sub (integrable_const (g v))).abs
  let B := fun ω => C*s+(|f ω (v+s)-g (v+s)|+
      |f ω (v-s)-g (v-s)|+2*|f ω v-g v|)/s
  have hi : Integrable B μ := (integrable_const (C*s)).add
    ((hp.add hn |>.add (hv.const_mul 2)).div_const s)
  have hb : ∀ᵐ ω ∂μ, |df ω-dg| ≤ B ω := by
    filter_upwards [hc,hd] with ω hω hω'
    exact convex_derivative_fluctuation hs hω hω' hplus hminus
  have hid : Integrable (fun ω => df ω-dg) μ :=
    hi.mono' (hm.sub aestronglyMeasurable_const) (by simpa only [Real.norm_eq_abs] using hb)
  refine ⟨?_,?_⟩
  · have hdi : Integrable (fun ω => (df ω-dg)+dg) μ := hid.add (integrable_const dg)
    simpa only [sub_add_cancel] using hdi
  have hib : Integrable (fun ω => (|f ω (v+s)-g (v+s)|+
      |f ω (v-s)-g (v-s)|+2*|f ω v-g v|)/s) μ :=
    (hp.add hn |>.add (hv.const_mul 2)).div_const s
  have hic : Integrable (fun ω => |f ω (v+s)-g (v+s)|+|f ω (v-s)-g (v-s)|) μ := hp.add hn
  have hie : Integrable (fun ω => 2*|f ω v-g v|) μ := hv.const_mul 2
  calc
    _ ≤ ∫ ω, B ω ∂μ := integral_mono_ae hid.abs hi hb
    _ = C*s+((∫ ω, |f ω (v+s)-g (v+s)| ∂μ)+
        (∫ ω, |f ω (v-s)-g (v-s)| ∂μ)+2*(∫ ω, |f ω v-g v| ∂μ))/s := by
      dsimp [B]
      rw [integral_add (integrable_const _) hib,
        integral_div,integral_add hic hie,integral_add hp hn,integral_const_mul]
      simp only [integral_const_mul,integral_const,probReal_univ,smul_eq_mul,one_mul]
    _ ≤ C*s+4*δ/s := by gcongr; linarith

lemma integral_tilted_ratio {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H F : X → ℝ) :
    (∫ x, F x ∂ν.tilted H) = (∫ x, Real.exp (H x)*F x ∂ν)/(∫ x, Real.exp (H x) ∂ν) := by
  rw [integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]

lemma measurable_random_tilted_integral {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H F : Ω × X → ℝ} (hH : Measurable H) (hF : Measurable F) :
    Measurable (fun ω => ∫ x, F (ω,x) ∂(ν ω).tilted (fun x => H (ω,x))) := by
  let κ : Kernel Ω X := ⟨ν,hν⟩
  have : IsMarkovKernel κ := ⟨fun ω => by change IsProbabilityMeasure (ν ω); infer_instance⟩
  simp_rw [integral_tilted_ratio]
  exact ((hH.exp.mul hF).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable.div
    ((hH.exp).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

lemma integrate_thermal_majorant {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T V : Ω → ℝ} {K C : ℝ}
    (hT : Measurable T) (hT0 : ∀ ω, 0 ≤ T ω) (hK : 0 < K)
    (hVi : Integrable V μ) (hVb : (∫ ω, V ω ∂μ) ≤ C)
    (hb : ∀ᵐ ω ∂μ, T ω ≤ (V ω+K^2)/(2*K)) :
    Integrable T μ ∧ (∫ ω, T ω ∂μ) ≤ (C+K^2)/(2*K) := by
  have hbI : Integrable (fun ω => (V ω+K^2)/(2*K)) μ :=
    (hVi.add (integrable_const _)).div_const _
  have hTi : Integrable T μ := hbI.mono' hT.aestronglyMeasurable
    (hb.mono fun ω hω => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hT0 ω)] using hω)
  refine ⟨hTi,(integral_mono_ae hTi hbI hb).trans ?_⟩
  rw [integral_div,integral_add hVi (integrable_const _),integral_const]
  simp only [probReal_univ,smul_eq_mul,one_mul]
  exact div_le_div_of_nonneg_right (by linarith : (∫ ω, V ω ∂μ)+K^2 ≤ C+K^2) (by positivity)

lemma measurable_random_thermal {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {Y : Ω × X → ℝ} (hY : Measurable Y) (v : ℝ) :
    Measurable (fun ω => ∫ x, |Y (ω,x)-(∫ z, Y (ω,z) ∂(ν ω).tilted (fun z => v*Y (ω,z)))|
      ∂(ν ω).tilted (fun x => v*Y (ω,x))) := by
  have hm := measurable_random_tilted_integral (ν := ν)
    (H := fun z : Ω × X => v*Y z) (F := Y) hν (hY.const_mul v) hY
  exact measurable_random_tilted_integral (ν := ν)
    (H := fun z : Ω × X => v*Y z)
    (F := fun z : Ω × X => |Y z-(∫ x, Y (z.1,x) ∂(ν z.1).tilted (fun x => v*Y (z.1,x)))|)
    hν (hY.const_mul v) (hY.sub (hm.comp measurable_fst) |>.abs)

theorem expected_tilted_thermal_at_minimum {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {Y : Ω × X → ℝ} (hY : Measurable Y) {v c a K : ℝ} (hK : 0 < K)
    (he : ∀ᵐ ω ∂μ, ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y (ω,x))) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (fun x => Y (ω,x)) (ν ω) t) μ)
    (hmin : IsLocalMin (fun t => -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)+c*(t-a)^2) v) :
    let m := fun ω => ∫ x, Y (ω,x) ∂(ν ω).tilted (fun x => v*Y (ω,x))
    let T := fun ω => ∫ x, |Y (ω,x)-m ω| ∂(ν ω).tilted (fun x => v*Y (ω,x))
    Integrable T μ ∧ (∫ ω, T ω ∂μ) ≤ (2*c+K^2)/(2*K) := by
  let m := fun ω => ∫ x, Y (ω,x) ∂(ν ω).tilted (fun x => v*Y (ω,x))
  let T := fun ω => ∫ x, |Y (ω,x)-m ω| ∂(ν ω).tilted (fun x => v*Y (ω,x))
  let V := fun ω => Var[(fun x => Y (ω,x)); (ν ω).tilted (fun x => v*Y (ω,x))]
  have hT : Measurable T := measurable_random_thermal hν hY v
  obtain ⟨hVi,hVb⟩ := expected_tilted_variance_at_minimum_ae (μ := μ) (v := v) (c := c) (a := a)
    ν (fun ω x => Y (ω,x)) he hi hmin
  change Integrable V μ at hVi
  change (∫ ω, V ω ∂μ) ≤ 2*c at hVb
  have hb : ∀ᵐ ω ∂μ, T ω ≤ (V ω+K^2)/(2*K) := by
    filter_upwards [he] with ω hω
    have : IsProbabilityMeasure ((ν ω).tilted (fun x => v*Y (ω,x))) :=
      isProbabilityMeasure_tilted (hω v)
    exact probability_thermal_young (by simpa using (memLp_tilted_mul
      (mem_interior_integrableExpSet_of_all hω v) (2:NNReal))) hK
  exact integrate_thermal_majorant (μ := μ) hT
    (fun _ => integral_nonneg (fun _ => abs_nonneg _)) hK hVi hVb hb

theorem expected_tilted_mean_at_minimum {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {Y : Ω × X → ℝ} (hY : Measurable Y) {v c a s δ : ℝ} (hs : 0 < s)
    (he : ∀ᵐ ω ∂μ, ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y (ω,x))) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (fun x => Y (ω,x)) (ν ω) t) μ)
    (hmin : ∀ t ∈ Icc (v-s) (v+s),
      -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) v ∂μ)+c*(v-a)^2 ≤
      -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)+c*(t-a)^2)
    (hconc : ∀ t ∈ ({v-s,v,v+s} : Set ℝ),
      (∫ ω, |cgf (fun x => Y (ω,x)) (ν ω) t -
        (∫ ω', cgf (fun x => Y (ω',x)) (ν ω') t ∂μ)| ∂μ) ≤ δ) :
    let m := fun ω => ∫ x, Y (ω,x) ∂(ν ω).tilted (fun x => v*Y (ω,x))
    Integrable m μ ∧ (∫ ω, |m ω-2*c*(v-a)| ∂μ) ≤ c*s+4*δ/s := by
  let m := fun ω => ∫ x, Y (ω,x) ∂(ν ω).tilted (fun x => v*Y (ω,x))
  have hm : Measurable m := measurable_random_tilted_integral (ν := ν)
    (H := fun z : Ω × X => v*Y z) (F := Y) hν (hY.const_mul v) hY
  apply integral_convex_derivative_fluctuation_ae (μ := μ) (v := v) (C := c)
    (dg := 2*c*(v-a)) (df := m) (δ := δ)
    (f := fun ω t => cgf (fun x => Y (ω,x)) (ν ω) t)
    (g := fun t => ∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ) hs
  · filter_upwards [he] with ω hω
    exact (convexOn_cgf_of_all_exp hω).subset (subset_univ _) (convex_Icc _ _)
  · filter_upwards [he] with ω hω
    have ht := mem_interior_integrableExpSet_of_all hω v
    have hd := (analyticAt_cgf ht).differentiableAt.hasDerivAt
    rwa [← integral_tilted_mul_self ht] at hd
  · have h := minimizer_quadratic_remainder (g := fun t => ∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)
      (v := v) (c := c) (a := a) (dg := 2*c*(v-a)) (x := v+s) (hmin (v+s) ⟨by linarith,le_rfl⟩) rfl
    simpa only [add_sub_cancel_left] using h
  · have h := minimizer_quadratic_remainder (g := fun t => ∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)
      (v := v) (c := c) (a := a) (dg := 2*c*(v-a)) (x := v-s) (hmin (v-s) ⟨le_rfl,by linarith⟩) rfl
    convert h using 1 <;> ring
  · exact hi _
  · exact hi _
  · exact hi _
  · exact hm.aestronglyMeasurable
  · exact hconc _ (by simp)
  · exact hconc _ (by simp)
  · exact hconc _ (by simp)

lemma probability_energy_triangle {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {Y : X → ℝ}
    (hY : Integrable Y ν) (b : ℝ) :
    (∫ x, |Y x-b| ∂ν) ≤ (∫ x, |Y x-(∫ z, Y z ∂ν)| ∂ν)+|(∫ z, Y z ∂ν)-b| := by
  let m := ∫ z, Y z ∂ν
  have hi : Integrable (fun x => |Y x-m|) ν := (hY.sub (integrable_const m)).abs
  calc
    _ ≤ ∫ x, |Y x-m|+|m-b| ∂ν := by
      apply integral_mono ((hY.sub (integrable_const b)).abs) (hi.add (integrable_const _))
      intro x
      exact abs_sub_le (Y x) m b
    _ = _ := by rw [integral_add hi (integrable_const _)]; simp [m]

theorem expected_tilted_energy_at_minimum {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {Y : Ω × X → ℝ} (hY : Measurable Y) {v c a s δ K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (he : ∀ᵐ ω ∂μ, ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y (ω,x))) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (fun x => Y (ω,x)) (ν ω) t) μ)
    (hmin : ∀ t ∈ Icc (v-s) (v+s),
      -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) v ∂μ)+c*(v-a)^2 ≤
      -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)+c*(t-a)^2)
    (hconc : ∀ t ∈ ({v-s,v,v+s} : Set ℝ),
      (∫ ω, |cgf (fun x => Y (ω,x)) (ν ω) t -
        (∫ ω', cgf (fun x => Y (ω',x)) (ν ω') t ∂μ)| ∂μ) ≤ δ) :
    let E := fun ω => ∫ x, |Y (ω,x)-2*c*(v-a)| ∂(ν ω).tilted (fun x => v*Y (ω,x))
    Integrable E μ ∧ (∫ ω, E ω ∂μ) ≤ (2*c+K^2)/(2*K)+c*s+4*δ/s := by
  let m := fun ω => ∫ x, Y (ω,x) ∂(ν ω).tilted (fun x => v*Y (ω,x))
  let T := fun ω => ∫ x, |Y (ω,x)-m ω| ∂(ν ω).tilted (fun x => v*Y (ω,x))
  let E := fun ω => ∫ x, |Y (ω,x)-2*c*(v-a)| ∂(ν ω).tilted (fun x => v*Y (ω,x))
  have hloc : IsLocalMin (fun t => -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)+c*(t-a)^2) v := by
    filter_upwards [Icc_mem_nhds (by linarith : v-s < v) (by linarith : v < v+s)] with t ht
    exact hmin t ht
  obtain ⟨hTi,hTb⟩ := expected_tilted_thermal_at_minimum hν hY hK he hi hloc
  obtain ⟨hmi,hmb⟩ := expected_tilted_mean_at_minimum hν hY hs he hi hmin hconc
  change Integrable T μ at hTi
  change (∫ ω, T ω ∂μ) ≤ _ at hTb
  change Integrable m μ at hmi
  change (∫ ω, |m ω-2*c*(v-a)| ∂μ) ≤ _ at hmb
  have hEi : Measurable E := measurable_random_tilted_integral (ν := ν)
    (H := fun z : Ω × X => v*Y z) (F := fun z => |Y z-2*c*(v-a)|)
    hν (hY.const_mul v) (hY.sub_const _ |>.abs)
  have hb : ∀ᵐ ω ∂μ, E ω ≤ T ω+|m ω-2*c*(v-a)| := by
    filter_upwards [he] with ω hω
    have : IsProbabilityMeasure ((ν ω).tilted (fun x => v*Y (ω,x))) := isProbabilityMeasure_tilted (hω v)
    exact probability_energy_triangle
      ((memLp_tilted_mul (mem_interior_integrableExpSet_of_all hω v) (1:NNReal)).integrable (by norm_num)) _
  have hbi : Integrable (fun ω => T ω+|m ω-2*c*(v-a)|) μ :=
    hTi.add ((hmi.sub (integrable_const _)).abs)
  have hE : Integrable E μ := hbi.mono' hEi.aestronglyMeasurable
    (hb.mono fun ω hω => by
      have hnonneg : 0 ≤ E ω := integral_nonneg (fun _ => abs_nonneg _)
      simpa only [Real.norm_eq_abs,abs_of_nonneg hnonneg] using hω)
  refine ⟨hE,(integral_mono_ae hE hbi hb).trans ?_⟩
  have hai : Integrable (fun ω => |m ω-2*c*(v-a)|) μ := (hmi.sub (integrable_const _)).abs
  rw [integral_add hTi hai]
  linarith

theorem random_gaussian_energy_at_minimum {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ B)
    {v c a s δ K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hmin : ∀ t ∈ Icc (v-s) (v+s),
      -(∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A x) z.2) (ν z.1) v
        ∂P.prod gaussianCoordinates)+c*(v-a)^2 ≤
      -(∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A x) z.2) (ν z.1) t
        ∂P.prod gaussianCoordinates)+c*(t-a)^2)
    (hconc : ∀ t ∈ ({v-s,v,v+s} : Set ℝ),
      (∫ z : Ω × (ℕ → ℝ), |cgf (fun x => cylinderField (A x) z.2) (ν z.1) t -
        (∫ z' : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A x) z'.2) (ν z'.1) t
          ∂P.prod gaussianCoordinates)| ∂P.prod gaussianCoordinates) ≤ δ) :
    let E := fun z : Ω × (ℕ → ℝ) => ∫ x, |cylinderField (A x) z.2-2*c*(v-a)|
      ∂(ν z.1).tilted (fun x => v*cylinderField (A x) z.2)
    Integrable E (P.prod gaussianCoordinates) ∧
      (∫ z, E z ∂P.prod gaussianCoordinates) ≤ (2*c+K^2)/(2*K)+c*s+4*δ/s := by
  let ν' : (Ω × (ℕ → ℝ)) → Measure X := fun z => ν z.1
  have hν' : Measurable ν' := hν.comp measurable_fst
  let Y : (Ω × (ℕ → ℝ)) × X → ℝ := fun z => cylinderField (A z.2) z.1.2
  have hY : Measurable Y := (measurable_cylinderFields A).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  exact expected_tilted_energy_at_minimum (μ := P.prod gaussianCoordinates)
    (ν := ν') (Y := Y) hν' hY hs hK (random_cylinder_all_exp_ae hν A hA)
    (integrable_random_cylinder_cgf hν A hA) hmin hconc

lemma tilted_singleton {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) (x : X) :
    (ν.tilted H) {x} = ENNReal.ofReal (Real.exp (H x)/referencePartition ν H)*ν {x} := by
  rw [tilted_apply,lintegral_singleton]; rfl

lemma replica_tilted_pi {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (r : ℕ) :
    (Measure.pi (fun _ : Fin r => ν)).tilted (fun σ => ∑ i, H (σ i)) =
      Measure.pi (fun _ : Fin r => ν.tilted H) := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted he
  have hz : 0 < referencePartition ν H := integral_exp_pos he
  apply Measure.ext_of_singleton
  intro σ
  rw [tilted_singleton,Measure.pi_singleton,Measure.pi_singleton]
  simp_rw [tilted_singleton]
  rw [show referencePartition (Measure.pi (fun _ : Fin r => ν)) (fun σ => ∑ i, H (σ i)) =
    (referencePartition ν H)^r from reference_replica_partition ν H r]
  rw [Real.exp_sum,ENNReal.ofReal_div_of_pos (pow_pos hz r),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),ENNReal.ofReal_pow hz.le]
  simp_rw [ENNReal.ofReal_div_of_pos hz]
  rw [Finset.prod_mul_distrib,ENNReal.prod_div_distrib_of_ne_top (fun _ _ => ENNReal.ofReal_ne_top)]
  simp

lemma referenceReplicaMean_eq_tilted {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean ν H D = ∫ σ, D σ ∂Measure.pi (fun _ : Fin r => ν.tilted H) := by
  rw [← replica_tilted_pi ν H he r,integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]
  rw [reference_replica_partition]; rfl

end IsingPerceptron

end

end OAI
