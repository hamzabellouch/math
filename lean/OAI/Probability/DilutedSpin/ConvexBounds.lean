import OAI.Probability.DilutedSpin.MixtureMeasures

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set
namespace DilutedSpinGlass

/-- The deterministic three-point estimate used in pert:convex-bound. It
requires convexity only on the original open parameter domain, not globally. -/
theorem convex_derivative_fluctuation {S : Set ℝ} {f g f' g' : ℝ → ℝ}
    (hf : ConvexOn ℝ S f) (hg : ConvexOn ℝ S g)
    {u ρ : ℝ} (hρ : 0 < ρ) (hm : u-ρ ∈ S) (hu : u ∈ S) (hp : u+ρ ∈ S)
    (hfu : HasDerivAt f (f' u) u)
    (hgm : HasDerivAt g (g' (u-ρ)) (u-ρ))
    (hgu : HasDerivAt g (g' u) u)
    (hgp : HasDerivAt g (g' (u+ρ)) (u+ρ)) :
    |f' u - g' u| ≤
      (|f (u-ρ) - g (u-ρ)| + 2*|f u-g u| + |f (u+ρ)-g (u+ρ)|) / ρ +
        g' (u+ρ) - g' (u-ρ) := by
  have hum : u-ρ < u := by linarith
  have hup : u < u+ρ := by linarith
  have hfm := hf.slope_le_of_hasDerivAt hm hu hum hfu
  have hfp := hf.le_slope_of_hasDerivAt hu hp hup hfu
  have hgml := hg.le_slope_of_hasDerivAt hm hu hum hgm
  have hgmr := hg.slope_le_of_hasDerivAt hm hu hum hgu
  have hgpl := hg.le_slope_of_hasDerivAt hu hp hup hgu
  have hgpr := hg.slope_le_of_hasDerivAt hu hp hup hgp
  have hd1 : u - (u-ρ) = ρ := by ring
  have hd2 : u+ρ - u = ρ := by ring
  simp only [slope_def_field, hd1, hd2] at hfm hfp hgml hgmr hgpl hgpr
  have hfm' := (div_le_iff₀ hρ).mp hfm
  have hfp' := (le_div_iff₀ hρ).mp hfp
  have hgml' := (le_div_iff₀ hρ).mp hgml
  have hgmr' := (div_le_iff₀ hρ).mp hgmr
  have hgpl' := (le_div_iff₀ hρ).mp hgpl
  have hgpr' := (div_le_iff₀ hρ).mp hgpr
  let A := |f (u-ρ)-g (u-ρ)| + 2*|f u-g u| + |f (u+ρ)-g (u+ρ)|
  have ha : (A / ρ) * ρ = A := div_mul_cancel₀ _ (ne_of_gt hρ)
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_left₀ hρ).mp
    dsimp only [A] at ha
    nlinarith [le_abs_self (f (u-ρ)-g (u-ρ)), neg_le_abs (f u-g u),
      abs_nonneg (f u-g u), abs_nonneg (f (u+ρ)-g (u+ρ))]
  · apply (mul_le_mul_iff_left₀ hρ).mp
    dsimp only [A] at ha
    nlinarith [le_abs_self (f (u+ρ)-g (u+ρ)), neg_le_abs (f u-g u),
      abs_nonneg (f u-g u), abs_nonneg (f (u-ρ)-g (u-ρ))]

end DilutedSpinGlass

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

 
theorem integral_abs_le_sqrt_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt (∫ x, (f x)^2 ∂μ) := by
  have hn := variance_nonneg (fun x => ‖f x‖) μ
  rw [variance_eq_sub hf.norm] at hn
  simp only [Real.norm_eq_abs, Pi.pow_apply, sq_abs] at hn
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))).mpr (by linarith)

theorem integral_deviation_le_sqrt_variance {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x-∫ y, f y ∂μ| ∂μ) ≤ Real.sqrt (variance f μ) := by
  have hh := integral_abs_le_sqrt_sq μ (hf.sub (memLp_const (∫ y, f y ∂μ)))
  change (∫ x, |f x-∫ y, f y ∂μ| ∂μ) ≤ Real.sqrt (∫ x, (f x-∫ y, f y ∂μ)^2 ∂μ) at hh
  rw [← variance_eq_integral hf.aemeasurable] at hh
  exact hh

omit [IsProbabilityMeasure μ] in
/-- Taking a root expectation preserves convexity on the original parameter
domain. This does not extend the perturbation outside its factor-positive
interval. -/
theorem convexOn_integral {S : Set ℝ} {F : Ω → ℝ → ℝ}
    (hS : Convex ℝ S) (hF : ∀ x, ConvexOn ℝ S (F x))
    (hi : ∀ u ∈ S, Integrable (fun x => F x u) μ) :
    ConvexOn ℝ S (fun u => ∫ x, F x u ∂μ) := by
  refine ⟨hS, ?_⟩
  intro a ha b hb w v hw hv hwv
  have huv : w*a+v*b ∈ S := hS ha hb hw hv hwv
  have hh := integral_mono (hi _ huv)
    (((hi a ha).const_mul w).add ((hi b hb).const_mul v))
    (fun x => (hF x).2 ha hb hw hv hwv)
  change (∫ x, F x (w*a+v*b) ∂μ) ≤ ∫ x, (w*F x a+v*F x b) ∂μ at hh
  rw [integral_add ((hi a ha).const_mul w) ((hi b hb).const_mul v), integral_const_mul,integral_const_mul] at hh
  simpa only [smul_eq_mul] using hh

/-- The probabilistic three-point convexity estimate, with its genuine
standard-deviation (rather than variance) scale. -/
theorem convex_derivative_mean_bound {S : Set ℝ} {F F' : Ω → ℝ → ℝ}
    {g g' : ℝ → ℝ} (hf : ∀ x, ConvexOn ℝ S (F x)) (hg : ConvexOn ℝ S g)
    {u ρ V : ℝ} (hρ : 0 < ρ)
    (hm : u-ρ ∈ S) (hu : u ∈ S) (hp : u+ρ ∈ S)
    (hfu : ∀ x, HasDerivAt (F x) (F' x u) u)
    (hgm : HasDerivAt g (g' (u-ρ)) (u-ρ))
    (hgu : HasDerivAt g (g' u) u) (hgp : HasDerivAt g (g' (u+ρ)) (u+ρ))
    (hD : Integrable (fun x => F' x u) μ)
    (hi : ∀ w ∈ S, MemLp (fun x => F x w) 2 μ)
    (he : ∀ w ∈ S, g w = ∫ x, F x w ∂μ)
    (hv : ∀ w ∈ S, variance (fun x => F x w) μ ≤ V) :
    (∫ x, |F' x u-g' u| ∂μ) ≤ 4*Real.sqrt V/ρ+g' (u+ρ)-g' (u-ρ) := by
  have hb (w : ℝ) (hw : w ∈ S) :
      (∫ x, |F x w-g w| ∂μ) ≤ Real.sqrt V := by
    rw [he w hw]
    exact (integral_deviation_le_sqrt_variance μ (hi w hw)).trans
      (Real.sqrt_le_sqrt (hv w hw))
  have hj (w : ℝ) (hw : w ∈ S) : Integrable (fun x => |F x w-g w|) μ :=
    (((hi w hw).integrable (by norm_num)).sub (integrable_const _)).abs
  have hbound := integral_mono ((hD.sub (integrable_const _)).abs)
    (((((hj (u-ρ) hm).add ((hj u hu).const_mul 2)).add (hj (u+ρ) hp)).div_const ρ).add
      (integrable_const (g' (u+ρ)-g' (u-ρ))))
    (fun x => by
      have hh := convex_derivative_fluctuation (hf x) hg hρ hm hu hp (hfu x) hgm hgu hgp
      change |F' x u-g' u| ≤ (|F x (u-ρ)-g (u-ρ)|+2*|F x u-g u|+|F x (u+ρ)-g (u+ρ)|)/ρ+(g' (u+ρ)-g' (u-ρ))
      linarith)
  have hv1 := hb (u-ρ) hm
  have hv2 := hb u hu
  have hv3 := hb (u+ρ) hp
  change (∫ x, |F' x u-g' u| ∂μ) ≤
    ∫ x, ((|F x (u-ρ)-g (u-ρ)|+2*|F x u-g u|+|F x (u+ρ)-g (u+ρ)|)/ρ+
      (g' (u+ρ)-g' (u-ρ))) ∂μ at hbound
  erw [integral_add
    ((((hj (u-ρ) hm).add ((hj u hu).const_mul 2)).add (hj (u+ρ) hp)).div_const ρ)
    (integrable_const _), integral_div,
    integral_add ((hj (u-ρ) hm).add ((hj u hu).const_mul 2)) (hj (u+ρ) hp),
    integral_add (hj (u-ρ) hm) ((hj u hu).const_mul 2), integral_const_mul,
    integral_const,probReal_univ,smul_eq_mul,one_mul] at hbound
  have hsum : ((∫ x, |F x (u-ρ)-g (u-ρ)| ∂μ)+2*(∫ x, |F x u-g u| ∂μ)+
      (∫ x, |F x (u+ρ)-g (u+ρ)| ∂μ))/ρ ≤ 4*Real.sqrt V/ρ :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hρ)
  linarith

end DilutedSpinGlass

namespace DilutedSpinGlass
open MeasureTheory Set intervalIntegral

/-- The boundary-layer estimate used in pert:convex-bound. It holds on the
specified finite domain only, including when the two boundary layers overlap. -/
theorem integral_monotone_shift {k : ℝ → ℝ} {a b ρ : ℝ}
    (hab : a ≤ b) (hρ : 0 ≤ ρ) (hk : MonotoneOn k (Icc (a-ρ) (b+ρ))) :
    (∫ u in a..b, k (u+ρ)-k (u-ρ)) ≤ 2*ρ*(k (b+ρ)-k (a-ρ)) := by
  have hlo : a-ρ ≤ b+ρ := by linarith
  have hint {x y : ℝ} (hx : x ∈ Icc (a-ρ) (b+ρ)) (hy : y ∈ Icc (a-ρ) (b+ρ)) :
      IntervalIntegrable k volume x y := by
    apply MonotoneOn.intervalIntegrable
    intro z hz w hw hzw
    apply hk _ _ hzw
    · change min x y ≤ z ∧ z ≤ max x y at hz
      exact ⟨le_trans (le_min hx.1 hy.1) hz.1, le_trans hz.2 (max_le hx.2 hy.2)⟩
    · change min x y ≤ w ∧ w ≤ max x y at hw
      exact ⟨le_trans (le_min hx.1 hy.1) hw.1, le_trans hw.2 (max_le hx.2 hy.2)⟩
  have ham : a-ρ ∈ Icc (a-ρ) (b+ρ) := ⟨le_rfl,hlo⟩
  have hap : a+ρ ∈ Icc (a-ρ) (b+ρ) := ⟨by linarith,by linarith⟩
  have hbm : b-ρ ∈ Icc (a-ρ) (b+ρ) := ⟨by linarith,by linarith⟩
  have hbp : b+ρ ∈ Icc (a-ρ) (b+ρ) := ⟨hlo,le_rfl⟩
  have hplus : IntervalIntegrable (fun u => k (u+ρ)) volume a b := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx y hy hxy
    exact hk ⟨by linarith [hx.1],by linarith [hx.2]⟩
      ⟨by linarith [hy.1],by linarith [hy.2]⟩ (by linarith)
  have hminus : IntervalIntegrable (fun u => k (u-ρ)) volume a b := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx y hy hxy
    exact hk ⟨by linarith [hx.1],by linarith [hx.2]⟩
      ⟨by linarith [hy.1],by linarith [hy.2]⟩ (by linarith)
  rw [integral_sub hplus hminus,integral_comp_add_right,integral_comp_sub_right]
  have he1 := integral_add_adjacent_intervals (hint ham hap) (hint hap hbp)
  have he2 := integral_add_adjacent_intervals (hint ham hbm) (hint hbm hbp)
  have hbnd := integral_mono_on (by linarith : b-ρ ≤ b+ρ) (hint hbm hbp)
    (intervalIntegrable_const (c := k (b+ρ))) (fun x hx =>
      hk ⟨by linarith [hx.1],hx.2⟩ hbp hx.2)
  have hand := integral_mono_on (by linarith : a-ρ ≤ a+ρ)
    (intervalIntegrable_const (c := k (a-ρ))) (hint ham hap) (fun x hx =>
      hk ham ⟨hx.1,by linarith [hx.2]⟩ hx.1)
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hbnd hand
  nlinarith

end DilutedSpinGlass

namespace DilutedSpinGlass
open MeasureTheory Set intervalIntegral

 
theorem integral_convex_derivative_bound {D k : ℝ → ℝ} {a b ρ V B : ℝ}
    (hab : a < b) (hρ : 0 < ρ)
    (hD : IntervalIntegrable D volume a b)
    (hk : MonotoneOn k (Icc (a-ρ) (b+ρ)))
    (hpoint : ∀ u ∈ Icc a b, D u ≤ 4*Real.sqrt V/ρ+k (u+ρ)-k (u-ρ))
    (hB : k (b+ρ)-k (a-ρ) ≤ B) :
    (∫ u in a..b, D u)/(b-a) ≤ 4*Real.sqrt V/ρ+(2*ρ*B)/(b-a) := by
  have hi {c : ℝ} (hc : -ρ ≤ c ∧ c ≤ ρ) :
      IntervalIntegrable (fun u => k (u+c)) volume a b := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le (le_of_lt hab)]
    intro x hx y hy hxy
    exact hk ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)
  have hp := hi (c := ρ) ⟨by linarith,le_rfl⟩
  have hm : IntervalIntegrable (fun u => k (u-ρ)) volume a b := by
    simpa only [sub_eq_add_neg] using (hi (c := -ρ) ⟨le_rfl,by linarith⟩)
  have hs := integral_monotone_shift (le_of_lt hab) (le_of_lt hρ) hk
  have hbnd := integral_mono_on (le_of_lt hab) hD
    ((intervalIntegrable_const (c := 4*Real.sqrt V/ρ)).add (hp.sub hm))
    (fun u hu => by simpa only [add_sub_assoc] using hpoint u hu)
  change (∫ u in a..b, D u) ≤ ∫ u in a..b, (4*Real.sqrt V/ρ+(k (u+ρ)-k (u-ρ))) at hbnd
  rw [integral_add intervalIntegrable_const (hp.sub hm),intervalIntegral.integral_const,
    smul_eq_mul] at hbnd
  have hB' := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 2*ρ)
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  have hne : b-a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  rw [add_mul,div_mul_cancel₀ _ hne]
  nlinarith

end DilutedSpinGlass

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem hasDerivAt_rootMean {F G : X → ℝ → ℝ} {S : Set ℝ}
    (hS : IsOpen S) (hFm : ∀ u, Measurable (fun x => F x u))
    (hGm : ∀ u, Measurable (fun x => G x u))
    (hi : ∀ u ∈ S, Integrable (fun x => F x u) μ)
    {B : X → ℝ} (hB : Integrable B μ) (hb : ∀ x u, u ∈ S → |G x u| ≤ B x)
    (hd : ∀ x u, u ∈ S → HasDerivAt (F x) (G x u) u) {u : ℝ} (hu : u ∈ S) :
    HasDerivAt (fun v => ∫ x, F x v ∂μ) (∫ x, G x u ∂μ) u := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (hS.mem_nhds hu)
    (Eventually.of_forall (fun v => (hFm v).aestronglyMeasurable)) (hi u hu)
    (hGm u).aestronglyMeasurable
    (ae_of_all _ (fun x v hv => by simpa only [Real.norm_eq_abs] using hb x v hv))
    hB (ae_of_all _ hd)).2

omit [IsProbabilityMeasure μ] in
theorem rootMean_abs_le {G : X → ℝ → ℝ} (hGm : ∀ u, Measurable (fun x => G x u))
    {B : X → ℝ} (hB : Integrable B μ) {u : ℝ} (hb : ∀ x, |G x u| ≤ B x) :
    |∫ x, G x u ∂μ| ≤ ∫ x, B x ∂μ := by
  exact (abs_integral_le_integral_abs).trans
    (integral_mono (hB.mono' (hGm u).aestronglyMeasurable (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using hb x))).abs hB hb)

/-- Root fluctuation estimate after averaging the actual convex score;
all differentiations of expectations are justified by the integrable
random count bound. -/
theorem root_derivative_integral_bound {F G : X → ℝ → ℝ} {S : Set ℝ}
    (hS : IsOpen S) (hSc : Convex ℝ S)
    (hFm : ∀ u, Measurable (fun x => F x u))
    (hGm : Measurable (fun z : X × ℝ => G z.1 z.2))
    (hfc : ∀ x, ConvexOn ℝ S (F x))
    (hLp : ∀ u ∈ S, MemLp (fun x => F x u) 2 μ)
    {B : X → ℝ} (hB : Integrable B μ) (hb : ∀ x u, u ∈ S → |G x u| ≤ B x)
    (hd : ∀ x u, u ∈ S → HasDerivAt (F x) (G x u) u)
    {a b ρ V : ℝ} (hab : a < b) (hρ : 0 < ρ)
    (hJ : Icc (a-ρ) (b+ρ) ⊆ S)
    (hv : ∀ u ∈ Icc (a-ρ) (b+ρ), variance (fun x => F x u) μ ≤ V) :
    (∫ u in a..b, (∫ x, |G x u-∫ y, G y u ∂μ| ∂μ))/(b-a) ≤
      4*Real.sqrt V/ρ+4*ρ*(∫ x, B x ∂μ)/(b-a) := by
  let g (u : ℝ) := ∫ x, F x u ∂μ
  let k (u : ℝ) := ∫ x, G x u ∂μ
  let D (u : ℝ) := ∫ x, |G x u-k u| ∂μ
  have hG (u : ℝ) : Measurable (fun x => G x u) :=
    hGm.comp (measurable_id.prodMk measurable_const)
  have hi (u : ℝ) (hu : u ∈ S) : Integrable (fun x => F x u) μ :=
    (hLp u hu).integrable (by norm_num)
  have hg : ConvexOn ℝ S g := convexOn_integral μ hSc hfc hi
  have hdg (u : ℝ) (hu : u ∈ S) : HasDerivAt g (k u) u :=
    hasDerivAt_rootMean μ hS hFm hG hi hB hb hd hu
  have hk : MonotoneOn k (Icc (a-ρ) (b+ρ)) := by
    intro x hx y hy hxy
    have hh := hg.monotoneOn_deriv (fun u hu => (hdg u hu).differentiableAt) (hJ hx) (hJ hy) hxy
    rwa [(hdg x (hJ hx)).deriv,(hdg y (hJ hy)).deriv] at hh
  have hki (u : ℝ) (hu : u ∈ S) : Integrable (fun x => G x u) μ :=
    hB.mono' (hG u).aestronglyMeasurable (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using hb x u hu))
  have hkab (u : ℝ) (hu : u ∈ S) : |k u| ≤ ∫ x, B x ∂μ :=
    rootMean_abs_le μ hG hB (fun x => hb x u hu)
  have hDm : Measurable D := by
    have hkm : Measurable k := (hGm.stronglyMeasurable.integral_prod_left').measurable
    exact (((hGm.sub (hkm.comp measurable_snd)).abs).stronglyMeasurable.integral_prod_left').measurable
  have hDb (u : ℝ) (hu : u ∈ Icc a b) : |D u| ≤ 2*(∫ x, B x ∂μ) := by
    have huS : u ∈ S := hJ ⟨by linarith [hu.1],by linarith [hu.2]⟩
    rw [abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
    have hh := integral_mono ((hki u huS).sub (integrable_const (k u))).abs
      (hB.add (integrable_const |k u|))
      (fun x => (abs_sub _ _).trans (add_le_add (hb x u huS) le_rfl))
    simp only [Pi.add_apply, Pi.sub_apply] at hh
    rw [integral_add hB (integrable_const _),integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
    dsimp only [D]
    linarith [hkab u huS]
  have hDi : IntervalIntegrable D volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    exact Measure.integrableOn_of_bounded (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      hDm.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioc
        (fun u hu => by simpa only [Real.norm_eq_abs] using hDb u ⟨hu.1.le,hu.2⟩))
  have hpoint (u : ℝ) (hu : u ∈ Icc a b) :
      D u ≤ 4*Real.sqrt V/ρ+k (u+ρ)-k (u-ρ) := by
    have hm : u-ρ ∈ Icc (a-ρ) (b+ρ) := ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have h0 : u ∈ Icc (a-ρ) (b+ρ) := ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have hp : u+ρ ∈ Icc (a-ρ) (b+ρ) := ⟨by linarith [hu.1],by linarith [hu.2]⟩
    apply convex_derivative_mean_bound μ
      (fun x => (hfc x).subset hJ (convex_Icc _ _)) (hg.subset hJ (convex_Icc _ _)) hρ hm h0 hp
      (fun x => hd x u (hJ h0)) (hdg _ (hJ hm)) (hdg _ (hJ h0)) (hdg _ (hJ hp))
      (hki u (hJ h0)) (fun w hw => hLp w (hJ hw)) (fun _ _ => rfl) hv
  have hB' : k (b+ρ)-k (a-ρ) ≤ 2*(∫ x, B x ∂μ) := by
    have hlo : a-ρ ≤ b+ρ := by linarith
    have h1 := hkab (b+ρ) (hJ ⟨hlo,le_rfl⟩)
    have h2 := hkab (a-ρ) (hJ ⟨le_rfl,hlo⟩)
    linarith [le_abs_self (k (b+ρ)), neg_abs_le (k (a-ρ))]
  have hh := integral_convex_derivative_bound hab hρ hDi hk hpoint hB'
  convert hh using 1; ring

end DilutedSpinGlass

end

end OAI
