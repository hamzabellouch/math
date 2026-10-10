import OAI.Probability.FKMaps.ExcursionKernel

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial

/-- Polar integration for an arbitrary nonnegative radial function in a plane. -/
lemma lintegral_plane (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p : ℝ×ℝ,F (Real.sqrt (p.1^2+p.2^2)))=
      ENNReal.ofReal (2*Real.pi)*∫⁻ r : ℝ in Ioi 0,ENNReal.ofReal r*F r := by
  rw [← lintegral_comp_polarCoord_symm]
  have he (r θ : ℝ) : (r*Real.cos θ)^2+(r*Real.sin θ)^2=r^2 := by
    nlinarith [Real.cos_sq_add_sin_sq θ]
  change (∫⁻ p : ℝ×ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal p.1 * F (Real.sqrt ((p.1*Real.cos p.2)^2+(p.1*Real.sin p.2)^2)))=_
  have hh : (∫⁻ p : ℝ×ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 * F (Real.sqrt ((p.1*Real.cos p.2)^2+(p.1*Real.sin p.2)^2)))=
      ∫⁻ p : ℝ×ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,ENNReal.ofReal p.1*F p.1 := by
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    dsimp only
    rw [he,Real.sqrt_sq hp.1.le]
  rw [hh]
  change (∫⁻ p : ℝ×ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,ENNReal.ofReal p.1*F p.1
    ∂(volume.prod volume))=_
  rw [setLIntegral_prod _ (by fun_prop)]
  simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo]
  have hv : Real.pi - -Real.pi=2*Real.pi := by ring
  rw [hv]
  exact (lintegral_mul_const (ENNReal.ofReal (2*Real.pi))
    (show Measurable (fun r : ℝ => ENNReal.ofReal r*F r) by fun_prop)).trans (mul_comm _ _)

lemma sqrt_sum_image (x : ℝ) :
    (fun r : ℝ => Real.sqrt (x^2+r^2)) '' Ioi 0=Ioi |x| := by
  ext s
  constructor
  · rintro ⟨r,hr,rfl⟩
    have hx : |x|=Real.sqrt (x^2) := (Real.sqrt_sq_eq_abs x).symm
    rw [mem_Ioi,hx,Real.sqrt_lt_sqrt_iff (sq_nonneg x)]
    nlinarith [sq_pos_of_pos (show 0<r from hr)]
  · intro hs
    have hsp : 0<s := (abs_nonneg x).trans_lt hs
    have hsub : 0<s^2-x^2 := by
      have hs : |x|<s := hs
      nlinarith [sq_abs x,abs_nonneg x]
    refine ⟨Real.sqrt (s^2-x^2),Real.sqrt_pos.mpr hsub,?_⟩
    dsimp only
    rw [Real.sq_sqrt hsub.le]
    convert Real.sqrt_sq hsp.le using 1
    congr 1
    ring

/-- Cylindrical radius substitution with its exact Jacobian. -/
lemma lintegral_radius_substitution (x : ℝ) (G : ℝ → ℝ≥0∞) :
    (∫⁻ r : ℝ in Ioi 0,ENNReal.ofReal r*G (Real.sqrt (x^2+r^2)))=
      ∫⁻ s : ℝ in Ioi |x|,ENNReal.ofReal s*G s := by
  have hd (r : ℝ) (hr : r∈Ioi (0:ℝ)) :
      HasDerivWithinAt (fun u : ℝ => Real.sqrt (x^2+u^2))
        (r/Real.sqrt (x^2+r^2)) (Ioi 0) r := by
    have hp : 0<x^2+r^2 := by nlinarith [sq_nonneg x,sq_pos_of_pos (show 0<r from hr)]
    have hd : HasDerivAt (fun u : ℝ => Real.sqrt (x^2+u^2))
        ((2*r)/(2*Real.sqrt (x^2+r^2))) r := by
      simpa only [Pi.pow_apply,id_eq,Nat.reduceSub,Nat.cast_ofNat,pow_one,mul_one] using
        (((hasDerivAt_id r).pow 2).const_add (x^2)).sqrt hp.ne'
    have he : (2*r)/(2*Real.sqrt (x^2+r^2))=r/Real.sqrt (x^2+r^2) := by ring
    rw [he] at hd
    exact hd.hasDerivWithinAt
  have hi : InjOn (fun r : ℝ => Real.sqrt (x^2+r^2)) (Ioi (0:ℝ)) := by
    intro a ha b hb hab
    have hh : x^2+a^2=x^2+b^2 := by
      have h := congrArg (fun u : ℝ => u^2) hab
      simpa only [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))] using h
    have ha : 0<a := ha
    have hb : 0<b := hb
    nlinarith
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd hi
    (fun s => ENNReal.ofReal s*G s)
  rw [sqrt_sum_image] at h
  rw [h]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr : 0<r := hr
  have hs : 0<Real.sqrt (x^2+r^2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg x,sq_pos_of_pos hr])
  dsimp only
  rw [abs_of_pos (div_pos hr hs),← mul_assoc,← ENNReal.ofReal_mul (div_nonneg hr.le hs.le),
    div_mul_cancel₀ _ hs.ne']

/-- Tonelli over the cylindrical slice `|x| < s`. -/
lemma lintegral_slice (G : ℝ×ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ x : ℝ,∫⁻ s : ℝ in Ioi |x|,G (x,s))=
      ∫⁻ s : ℝ in Ioi 0,∫⁻ x : ℝ in Ioo (-s) s,G (x,s) := by
  have hmeas : Measurable (fun p : ℝ×ℝ => if |p.1|<p.2 then G p else 0) := by
    exact hG.ite (measurableSet_lt (measurable_fst.abs) measurable_snd) measurable_const
  have hleft : (∫⁻ x : ℝ,∫⁻ s : ℝ in Ioi |x|,G (x,s))=
      ∫⁻ x : ℝ,∫⁻ s : ℝ,if |x|<s then G (x,s) else 0 := by
    apply lintegral_congr
    intro x
    rw [← lintegral_indicator measurableSet_Ioi]
    rfl
  rw [hleft,lintegral_lintegral_swap hmeas.aemeasurable,← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro s
  by_cases hs : 0<s
  · rw [Set.indicator_of_mem (show s∈Ioi (0:ℝ) from hs),← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro x
    simp only [Set.indicator,Set.mem_Ioo,abs_lt]
  · rw [Set.indicator_of_notMem (show s∉Ioi (0:ℝ) from hs)]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [] with x
    have hh : ¬|x|<s := by linarith [abs_nonneg x]
    simp [hh]

/-- Three-dimensional radial integration, disintegrated along the first coordinate.
This supplies the radial noncentral-Gaussian transition without assuming a Bessel law. -/
theorem lintegral_cylindrical (G : ℝ×ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ p : ℝ×(ℝ×ℝ),G (p.1,Real.sqrt (p.1^2+p.2.1^2+p.2.2^2)))=
      ENNReal.ofReal (2*Real.pi)*
        ∫⁻ s : ℝ in Ioi 0,ENNReal.ofReal s*∫⁻ x : ℝ in Ioo (-s) s,G (x,s) := by
  change (∫⁻ p : ℝ×(ℝ×ℝ),G (p.1,Real.sqrt (p.1^2+p.2.1^2+p.2.2^2))
    ∂(volume.prod volume))=_
  rw [lintegral_prod _ (by fun_prop)]
  have hg (x : ℝ) : Measurable (fun r : ℝ => G (x,Real.sqrt (x^2+r^2))) := by fun_prop
  have hplane (x : ℝ) :
      (∫⁻ p : ℝ×ℝ,G (x,Real.sqrt (x^2+p.1^2+p.2^2)))=
      ENNReal.ofReal (2*Real.pi)*∫⁻ s : ℝ in Ioi |x|,ENNReal.ofReal s*G (x,s) := by
    have h := lintegral_plane (fun r => G (x,Real.sqrt (x^2+r^2))) (hg x)
    simp only [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))] at h
    simp only [← add_assoc] at h
    rw [h]
    congr 1
    exact lintegral_radius_substitution x (fun s => G (x,s))
  simp_rw [hplane]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [lintegral_slice (fun p => ENNReal.ofReal p.2*G p) (by fun_prop)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s _
  exact lintegral_const_mul' (ENNReal.ofReal s) (fun x => G (x,s)) ENNReal.ofReal_ne_top

end FKCRT.Radial
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

/-- Radial transition density of three-dimensional Brownian motion. -/
def radialHeat (t r s : ℝ) : ℝ :=
  if r=0 then 2*s^2/t*heat t s else s/r*killedHeat t r s

/-- Gaussian density in cylindrical coordinates, with the axial coordinate remaining. -/
def cylindricalDensity (t r s x : ℝ) : ℝ :=
  Real.exp (-(s^2+r^2)/(2*t))/(Real.sqrt (2*Real.pi*t))^3 * Real.exp (r*x/t)

lemma cylindricalDensity_continuous (t r : ℝ) :
    Continuous (fun p : ℝ×ℝ => cylindricalDensity t r p.2 p.1) := by
  unfold cylindricalDensity
  fun_prop

lemma cylindricalDensity_nonneg {t : ℝ} (ht : 0<t) (r s x : ℝ) :
    0≤cylindricalDensity t r s x := by
  unfold cylindricalDensity
  positivity

lemma cylindricalDensity_endpoint {t : ℝ} (ht : 0<t) (r s : ℝ) :
    cylindricalDensity t r s s=heat t (s-r)/(2*Real.pi*t) := by
  have hS : (Real.sqrt (2*Real.pi*t))^2=2*Real.pi*t := Real.sq_sqrt (by positivity)
  have hSn : Real.sqrt (2*Real.pi*t)≠0 := by positivity
  have he : -(s^2+r^2)/(2*t)+r*s/t= -(s-r)^2/(2*t) := by ring
  unfold cylindricalDensity heat
  rw [div_mul_eq_mul_div,← Real.exp_add,he]
  rw [show (Real.sqrt (2*Real.pi*t))^3=Real.sqrt (2*Real.pi*t)*(2*Real.pi*t) by
    calc
      _ = Real.sqrt (2*Real.pi*t)*(Real.sqrt (2*Real.pi*t))^2 := by ring
      _ = _ := by rw [hS]]
  field_simp

lemma cylindricalDensity_neg_endpoint {t : ℝ} (ht : 0<t) (r s : ℝ) :
    cylindricalDensity t r s (-s)=heat t (s+r)/(2*Real.pi*t) := by
  have h := cylindricalDensity_endpoint ht r (-s)
  have he : cylindricalDensity t r (-s) (-s)=cylindricalDensity t r s (-s) := by
    simp only [cylindricalDensity,neg_sq]
  rw [he] at h
  rw [h]
  simp only [heat,show (-s-r)^2=(s+r)^2 by ring]

lemma integral_exp_linear {k : ℝ} (hk : k≠0) {s : ℝ} (hs : 0≤ s) :
    (∫ x : ℝ in Ioo (-s) s,Real.exp (k*x))=(Real.exp (k*s)-Real.exp (k*(-s)))/k := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (k*y)/k) (Real.exp (k*x)) x := by
    have h := (((hasDerivAt_id x).const_mul k).exp).div_const k
    simpa only [id_eq,mul_one,mul_div_cancel_right₀ _ hk] using h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (show IntervalIntegrable (fun x : ℝ => Real.exp (k*x)) volume (-s) s from
      (by fun_prop : Continuous (fun x : ℝ => Real.exp (k*x))).intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le (by linarith),integral_Ioc_eq_integral_Ioo] at h
  exact h.trans (by ring)

/-- Angular integration gives the reflection-kernel formula, including the entrance r=0. -/
theorem cylindrical_integral {t r s : ℝ} (ht : 0<t) (hr : 0≤r) (hs : 0≤ s) :
    2*Real.pi*s*(∫ x : ℝ in Ioo (-s) s,cylindricalDensity t r s x)=radialHeat t r s := by
  have hS : (Real.sqrt (2*Real.pi*t))^2=2*Real.pi*t := Real.sq_sqrt (by positivity)
  have hSn : Real.sqrt (2*Real.pi*t)≠0 := by positivity
  have htn : t≠0 := ht.ne'
  have hπ : Real.pi≠0 := Real.pi_ne_zero
  by_cases hr0 : r=0
  · subst r
    have he : (fun x : ℝ => cylindricalDensity t 0 s x)=
        fun _ : ℝ => Real.exp (-s^2/(2*t))/(Real.sqrt (2*Real.pi*t))^3 := by
      funext x
      simp [cylindricalDensity]
    rw [he,setIntegral_const,Real.volume_real_Ioo,max_eq_left (by linarith)]
    simp only [radialHeat,ite_true,smul_eq_mul,heat]
    have heS : (Real.sqrt (2*Real.pi*t))^3=Real.sqrt (2*Real.pi*t)*(2*Real.pi*t) := by
      calc
        _ = Real.sqrt (2*Real.pi*t)*(Real.sqrt (2*Real.pi*t))^2 := by ring
        _ = _ := by rw [hS]
    rw [heS]
    field_simp [htn,hπ,hSn]
    all_goals ring
  · have hrp : 0<r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hk : r/t≠0 := (div_pos hrp ht).ne'
    have hi : (∫ x : ℝ in Ioo (-s) s,cylindricalDensity t r s x)=
        (t/r)*(cylindricalDensity t r s s-cylindricalDensity t r s (-s)) := by
      unfold cylindricalDensity
      have he : (fun x : ℝ => Real.exp (r*x/t))=fun x : ℝ => Real.exp ((r/t)*x) := by
        funext x
        congr 1
        ring
      rw [integral_const_mul,he,integral_exp_linear hk hs]
      rw [show (r/t)*s=r*s/t by ring,show (r/t)*(-s)=r*(-s)/t by ring]
      field_simp [htn,hr0]
    rw [hi,cylindricalDensity_endpoint ht,cylindricalDensity_neg_endpoint ht]
    simp only [radialHeat,ite_eq_right hr0,killedHeat]
    field_simp [htn,hπ,hSn]

lemma radialHeat_nonneg {t r s : ℝ} (ht : 0<t) (hr : 0≤r) (hs : 0≤ s) :
    0≤radialHeat t r s := by
  rw [← cylindrical_integral ht hr hs]
  exact mul_nonneg (by positivity) (integral_nonneg (fun x => cylindricalDensity_nonneg ht _ _ _))

lemma cylindricalDensity_of_norm {t : ℝ} (ht : 0<t) (r x y z : ℝ) :
    cylindricalDensity t r (Real.sqrt (x^2+y^2+z^2)) x=
      heat t (x-r)*heat t y*heat t z := by
  have hS : Real.sqrt (2*Real.pi*t)≠0 := by positivity
  have hs : (Real.sqrt (x^2+y^2+z^2))^2=x^2+y^2+z^2 := Real.sq_sqrt (by positivity)
  unfold cylindricalDensity heat
  rw [hs,div_mul_eq_mul_div,← Real.exp_add]
  rw [div_mul_div_comm,div_mul_div_comm,← Real.exp_add,← Real.exp_add]
  congr 1
  · congr 1
    ring
  · ring

/-- Exact radial image of the genuinely shifted three independent Gaussian densities.
The formula is a proved change of variables, not a Bessel-process assumption. -/
theorem lintegral_radial_gaussian {t r : ℝ} (ht : 0<t) (hr : 0≤r)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p : ℝ×(ℝ×ℝ), ENNReal.ofReal (heat t (p.1-r)*heat t p.2.1*heat t p.2.2)*
      F (Real.sqrt (p.1^2+p.2.1^2+p.2.2^2)))=
      ∫⁻ s : ℝ in Ioi 0,ENNReal.ofReal (radialHeat t r s)*F s := by
  have hc := cylindricalDensity_continuous t r
  have hh := Radial.lintegral_cylindrical
    (fun p : ℝ×ℝ => ENNReal.ofReal (cylindricalDensity t r p.2 p.1)*F p.2)
    (hc.measurable.ennreal_ofReal.mul (hF.comp measurable_snd))
  simp only [cylindricalDensity_of_norm ht] at hh
  rw [hh,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs
  have hs : 0<s := hs
  dsimp only
  have hD : Continuous (fun x : ℝ => cylindricalDensity t r s x) := by
    unfold cylindricalDensity
    fun_prop
  rw [lintegral_mul_const _ (hD.measurable.ennreal_ofReal),
    ← ofReal_integral_eq_lintegral_ofReal (hD.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      (Filter.Eventually.of_forall (fun x => cylindricalDensity_nonneg ht r s x))]
  rw [← mul_assoc,← mul_assoc,← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),cylindrical_integral ht hr hs.le]

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma heat_neg (t r : ℝ) : heat t (-r)=heat t r := by simp [heat]

/-- The elementary Gaussian bridge identity with its exact normalizing constants. -/
lemma heat_bridge {A B : ℝ} (hB : 0<B) (hBA : B<A) (r s : ℝ) :
    heat ((A-B)*B/A) (s-(B/A)*r)*heat A r=heat (A-B) (s-r)*heat B s := by
  have hA : 0<A := hB.trans hBA
  have hd : 0<A-B := sub_pos.mpr hBA
  have hv : 0<(A-B)*B/A := by positivity
  have hden : Real.sqrt (2*Real.pi*((A-B)*B/A))*Real.sqrt (2*Real.pi*A)=
      Real.sqrt (2*Real.pi*(A-B))*Real.sqrt (2*Real.pi*B) := by
    rw [← Real.sqrt_mul (by positivity),← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hexp : -(s-(B/A)*r)^2/(2*((A-B)*B/A))-r^2/(2*A)=
      -(s-r)^2/(2*(A-B))-s^2/(2*B) := by
    field_simp
    ring
  unfold heat
  rw [div_mul_div_comm,div_mul_div_comm,← Real.exp_add,← Real.exp_add,hden]
  congr 1
  congr 1
  simpa only [sub_eq_add_neg,neg_div] using hexp

/-- Gaussian regression and the radial heat transform agree, including radius zero. -/
theorem radialHeat_bridge {A B : ℝ} (hB : 0<B) (hBA : B<A) (r s : ℝ) :
    radialHeat ((A-B)*B/A) ((B/A)*r) s=
      radialHeat (A-B) r s*((A/B)*heat B s/heat A r) := by
  have hA : 0<A := hB.trans hBA
  have hd : 0<A-B := sub_pos.mpr hBA
  have hc : B/A≠0 := div_ne_zero hB.ne' hA.ne'
  have hh : heat A r≠0 := (heat_pos hA r).ne'
  have hminus := heat_bridge hB hBA r s
  have hplus := heat_bridge hB hBA (-r) s
  simp only [heat_neg,mul_neg,sub_neg_eq_add] at hplus
  by_cases hr : r=0
  · subst r
    simp only [mul_zero,radialHeat]
    -- Keep the normalizing Gaussian product rather than squaring any density.
    have he : heat ((A-B)*B/A) s=heat (A-B) s*heat B s/heat A 0 := by
      apply (eq_div_iff (heat_pos hA 0).ne').mpr
      simpa only [mul_zero,sub_zero] using heat_bridge hB hBA 0 s
    change 2*s^2/((A-B)*B/A)*heat ((A-B)*B/A) s=
      (2*s^2/(A-B)*heat (A-B) s)*((A/B)*heat B s/heat A 0)
    rw [he]
    field_simp
  · have hcr : (B/A)*r≠0 := mul_ne_zero hc hr
    simp only [radialHeat,ite_eq_right hcr,ite_eq_right hr,killedHeat]
    apply (mul_right_cancel₀ hh)
    calc
      (s/(B/A*r)*(heat ((A-B)*B/A) (s-(B/A)*r)-heat ((A-B)*B/A) (s+(B/A)*r)))*heat A r
          =s/(B/A*r)*(heat (A-B) (s-r)-heat (A-B) (s+r))*heat B s := by
            calc
              _=s/(B/A*r)*(heat ((A-B)*B/A) (s-(B/A)*r)*heat A r-
                heat ((A-B)*B/A) (s+(B/A)*r)*heat A r) := by ring
              _=_ := by rw [hminus,hplus]; ring
      _=(s/r*(heat (A-B) (s-r)-heat (A-B) (s+r))*((A/B)*heat B s/heat A r))*heat A r := by
        field_simp

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

def hitHeat (t x : ℝ) : ℝ := 2*x/t*heat t x

lemma hitHeat_pos {t x : ℝ} (ht : 0<t) (hx : 0<x) : 0<hitHeat t x :=
  mul_pos (div_pos (mul_pos (by norm_num) hx) ht) (heat_pos ht x)

/-- Positive-radius bridge transition, directly from the reflected kernels and
the terminal ballot factor. -/
lemma conditioned_kernel_limit {J R T a b : ℕ → ℕ} {s t x y : ℝ}
    (hs : 0<s) (ht : 0<t) (hx : 0<x)
    (hJ : Tendsto J atTop atTop) (hR : Tendsto R atTop atTop)
    (hT : Tendsto T atTop atTop)
    (hrJ : Tendsto (fun n => (J n:ℝ)/(T n:ℝ)) atTop (𝓝 s))
    (hrR : Tendsto (fun n => ((R n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 t))
    (hzJ : ∀ᶠ n in atTop,Even ((J n:ℤ)+(b n:ℤ)-a n))
    (hzR : ∀ᶠ n in atTop,Even (((R n+1:ℕ):ℤ)+((b n:ℤ)+1)))
    (hzA : ∀ᶠ n in atTop,Even (((J n+R n+1:ℕ):ℤ)+((a n:ℤ)+1)))
    (ha : Tendsto (fun n => (a n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 x))
    (hb : Tendsto (fun n => (b n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 y)) :
    Tendsto (fun n => Real.sqrt (T n:ℝ)/2*
      (killed (J n) (a n) (b n)*pathMass (R n+1) (firstHit (b n)) /
        pathMass (J n+R n+1) (firstHit (a n)))) atTop
      (𝓝 (radialHeat (s*t/(s+t)) (t/(s+t)*x) y)) := by
  have hJR : Tendsto (fun n => J n+R n) atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_add_right _ _) hJ
  have hrJR : Tendsto (fun n => (((J n+R n:ℕ):ℝ)+1)/(T n:ℝ)) atTop (𝓝 (s+t)) := by
    convert hrJ.add hrR using 1; simp [add_div,add_assoc]
  have hk := killed_scaled_limit hs hJ hT hrJ hzJ ha hb
  have hr := firstHit_scaled_limit ht hR hT hrR hzR hb
  have hd := firstHit_scaled_limit (add_pos hs ht) hJR hT hrJR hzA ha
  have hd0 := hitHeat_pos (add_pos hs ht) hx
  have hlimit := ((hk.mul hr).div hd hd0.ne').div_const 2
  have he : ((2*killedHeat s x y)*(2*y/t*heat t y)/(2*x/(s+t)*heat (s+t) x))/2=
      radialHeat (s*t/(s+t)) (t/(s+t)*x) y := by
    have hh := radialHeat_bridge ht (by linarith : t<s+t) x y
    rw [show s+t-t=s by ring] at hh
    rw [hh,radialHeat,ite_eq_right hx.ne']
    field_simp
  rw [he] at hlimit
  apply hlimit.congr'
  filter_upwards [hT.eventually (eventually_gt_atTop 0)] with n hn
  have hn0 : (T n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  dsimp only [Pi.div_apply,Pi.mul_apply]
  field_simp

lemma firstHit_zero_scaled_limit {D T : ℕ → ℕ} {u : ℝ}
    (hu : 0<u) (hD : Tendsto D atTop atTop) (hT : Tendsto T atTop atTop)
    (hr : Tendsto (fun n => ((D n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 u))
    (hz : ∀ᶠ n in atTop,Even (((D n+1:ℕ):ℤ)+1)) :
    Tendsto (fun n => (T n:ℝ)*Real.sqrt (T n:ℝ)*pathMass (D n+1) (firstHit 0))
      atTop (𝓝 (2/u*heat u 0)) := by
  have hD' : Tendsto (fun n => D n+1) atTop atTop := tendsto_atTop_mono (fun n => by omega) hD
  have hk := kernel_scaled_limit hu hD' hT
    (by simpa only [Nat.cast_add,Nat.cast_one] using hr) hz
    (by simpa only [Int.cast_one] using cast_div_sqrt_tendsto_zero hT 1)
  have hh := hk.div hr hu.ne'
  have he : (2*heat u 0)/u=2/u*heat u 0 := by ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [hT.eventually (eventually_gt_atTop 0)] with n hn
  have ht0 : (T n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [firstHit_formula]
  dsimp only [Pi.div_apply]
  norm_num only [Nat.cast_zero,Int.natCast_zero,zero_add]
  field_simp

lemma entrance_conditioned_limit {J R T b : ℕ → ℕ} {s t y : ℝ}
    (hs : 0<s) (ht : 0<t)
    (hJ : Tendsto J atTop atTop) (hR : Tendsto R atTop atTop)
    (hT : Tendsto T atTop atTop)
    (hrJ : Tendsto (fun n => (J n:ℝ)/(T n:ℝ)) atTop (𝓝 s))
    (hrR : Tendsto (fun n => ((R n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 t))
    (hzJ : ∀ᶠ n in atTop,Even ((J n:ℤ)+(b n:ℤ)))
    (hzR : ∀ᶠ n in atTop,Even (((R n+1:ℕ):ℤ)+((b n:ℤ)+1)))
    (hzA : ∀ᶠ n in atTop,Even (((J n+R n+1:ℕ):ℤ)+1))
    (hb : Tendsto (fun n => (b n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 y)) :
    Tendsto (fun n => Real.sqrt (T n:ℝ)/2*
      (killed (J n) 0 (b n)*pathMass (R n+1) (firstHit (b n)) /
        pathMass (J n+R n+1) (firstHit 0))) atTop
      (𝓝 (radialHeat (s*t/(s+t)) 0 y)) := by
  have hJR : Tendsto (fun n => J n+R n) atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_add_right _ _) hJ
  have hrJR : Tendsto (fun n => (((J n+R n:ℕ):ℝ)+1)/(T n:ℝ)) atTop (𝓝 (s+t)) := by
    convert hrJ.add hrR using 1; simp [add_div,add_assoc]
  have hk := entrance_scaled_limit hs hJ hT hrJ hzJ hb
  have hr := firstHit_scaled_limit ht hR hT hrR hzR hb
  have hd := firstHit_zero_scaled_limit (add_pos hs ht) hJR hT hrJR hzA
  have hd0 : 0<2/(s+t)*heat (s+t) 0 := mul_pos (div_pos (by norm_num) (add_pos hs ht)) (heat_pos (add_pos hs ht) 0)
  have hlimit := ((hk.mul hr).div hd hd0.ne').div_const 2
  have he : ((4*y/s*heat s y)*(2*y/t*heat t y)/(2/(s+t)*heat (s+t) 0))/2=
      radialHeat (s*t/(s+t)) 0 y := by
    have hh := radialHeat_bridge ht (by linarith : t<s+t) 0 y
    rw [mul_zero,show s+t-t=s by ring] at hh
    rw [hh]
    rw [show radialHeat s 0 y=2*y^2/s*heat s y by simp [radialHeat]]
    field_simp
    ring
  rw [he] at hlimit
  apply hlimit.congr'
  filter_upwards [hT.eventually (eventually_gt_atTop 0)] with n hn
  have hn0 : (T n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hs0 : Real.sqrt (T n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have hsq := Real.sq_sqrt (show 0≤(T n:ℝ) from Nat.cast_nonneg _)
  dsimp only [Pi.div_apply,Pi.mul_apply]
  field_simp
  rw [hsq]
  ring

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory WithLp
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open SimpleWalk
abbrev Space := EuclideanSpace ℝ (Fin 3)

def axis (r : ℝ) : Space := toLp 2 ![r,0,0]

def step (t : ℝ) (v : Space) : Measure Space :=
  (stdGaussian Space).map (fun z => v+Real.sqrt t • z)

instance step_probability (t : ℝ) (v : Space) : IsProbabilityMeasure (step t v) := by
  unfold step
  infer_instance

lemma norm_axis (r : ℝ) : ‖axis r‖=|r| := by
  unfold axis
  have h := EuclideanSpace.real_norm_sq_eq (toLp 2 ![r,0,0])
  simp [Fin.sum_univ_succ] at h
  nlinarith [norm_nonneg (toLp 2 ![r,0,0]),abs_nonneg r,sq_abs r]

lemma gaussian_affine (a : ℝ) {t : ℝ} (ht : 0≤t) :
    (gaussianReal 0 1).map (fun x => a+Real.sqrt t*x)=gaussianReal a (⟨t,ht⟩ : ℝ≥0) := by
  have he : (fun x : ℝ => a+Real.sqrt t*x)=(fun x : ℝ => a+x) ∘ (fun x : ℝ => Real.sqrt t*x) := rfl
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop),gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  simp only [mul_zero,zero_add,mul_one]
  congr 1
  exact NNReal.eq (Real.sq_sqrt ht)

/-- The orthogonally invariant Gaussian step is exactly the product of its three coordinates. -/
theorem step_coordinates {t : ℝ} (ht : 0≤t) (v : Space) :
    step t v=(Measure.pi (fun i : Fin 3 => gaussianReal (v i) (⟨t,ht⟩ : ℝ≥0))).map (toLp 2) := by
  let f : Fin 3 → ℝ → ℝ := fun i x => v i+Real.sqrt t*x
  have hfm (i : Fin 3) : Measurable (f i) := by fun_prop
  have (i : Fin 3) : IsProbabilityMeasure ((gaussianReal 0 1).map (f i)) :=
    inferInstance
  have hp : (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)).map (fun x i => f i (x i))=
      Measure.pi (fun i : Fin 3 => gaussianReal (v i) (⟨t,ht⟩ : ℝ≥0)) := by
    rw [Measure.pi_map_pi (fun i => (hfm i).aemeasurable)]
    congr 1
    funext i
    exact gaussian_affine _ ht
  unfold step
  rw [← map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop),← hp,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

lemma step_rotation (t : ℝ) (v : Space) (U : Space ≃ₗᵢ[ℝ] Space) :
    (step t v).map U=step t (U v) := by
  unfold step
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun z => U (v+Real.sqrt t • z))=(fun z => U v+Real.sqrt t • z) ∘ U := by
    funext z
    simp
  change (stdGaussian Space).map (fun z => U (v+Real.sqrt t • z))=_
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop),stdGaussian_map]

lemma step_norm_rotation (t : ℝ) (v : Space) (U : Space ≃ₗᵢ[ℝ] Space) :
    (step t (U v)).map (fun z => ‖z‖)=(step t v).map (fun z => ‖z‖) := by
  rw [← step_rotation t v U,Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  exact U.norm_map z

lemma step_norm_axis (t : ℝ) (v : Space) :
    (step t v).map (fun z => ‖z‖)=(step t (axis ‖v‖)).map (fun z => ‖z‖) := by
  let U : Space ≃ₗᵢ[ℝ] Space := Submodule.reflection (ℝ ∙ (v-axis ‖v‖))ᗮ
  have hU : U v=axis ‖v‖ := by
    apply Submodule.reflection_sub
    rw [norm_axis,abs_of_nonneg (norm_nonneg v)]
  rw [← hU]
  exact (step_norm_rotation t v U).symm

def coordinates : (Fin 3 → ℝ) ≃ᵐ ℝ×(ℝ×ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)

lemma coordinates_apply (f : Fin 3 → ℝ) : coordinates f=(f 0,(f 1,f 2)) := rfl
lemma coordinates_symm_apply (p : ℝ×(ℝ×ℝ)) : coordinates.symm p=![p.1,p.2.1,p.2.2] := by
  apply coordinates.injective
  rw [MeasurableEquiv.apply_symm_apply,coordinates_apply]
  rfl

lemma coordinates_preserving (μ : Fin 3 → Measure ℝ) [∀ i,SigmaFinite (μ i)] :
    MeasurePreserving coordinates (Measure.pi μ) ((μ 0).prod ((μ 1).prod (μ 2))) := by
  have h0 := measurePreserving_piFinSuccAbove μ 0
  have (i : Fin 2) : SigmaFinite (![μ 1,μ 2] i) := by
    fin_cases i <;> dsimp <;> infer_instance
  have h1 := (MeasurePreserving.id (μ 0)).prod (measurePreserving_finTwoArrow_vec (μ 1) (μ 2))
  have he : (fun j : Fin 2 => μ ((0 : Fin 3).succAbove j))=![μ 1,μ 2] := by
    funext j
    fin_cases j <;> rfl
  rw [he] at h0
  exact h1.comp h0

lemma norm_coordinates (p : ℝ×(ℝ×ℝ)) :
    ‖toLp 2 (coordinates.symm p)‖=Real.sqrt (p.1^2+p.2.1^2+p.2.2^2) := by
  rw [coordinates_symm_apply]
  have h := EuclideanSpace.real_norm_sq_eq (toLp 2 ![p.1,p.2.1,p.2.2])
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero] at h
  have hs := Real.sq_sqrt (show 0≤p.1^2+p.2.1^2+p.2.2^2 by positivity)
  nlinarith [norm_nonneg (toLp 2 ![p.1,p.2.1,p.2.2]),Real.sqrt_nonneg (p.1^2+p.2.1^2+p.2.2^2)]

lemma heat_gaussianPDF (a : ℝ) {t : ℝ} (ht : 0≤t) (x : ℝ) :
    gaussianPDF a (⟨t,ht⟩ : ℝ≥0) x=ENNReal.ofReal (heat t (x-a)) := by
  change ENNReal.ofReal (gaussianPDFReal a (⟨t,ht⟩ : ℝ≥0) x)=_
  congr 1
  simp only [gaussianPDFReal,heat,div_eq_mul_inv]
  change (Real.sqrt (2*Real.pi*t))⁻¹ * Real.exp (-(x-a)^2*(2*t)⁻¹) =
    Real.exp (-(x-a)^2*(2*t)⁻¹)*(Real.sqrt (2*Real.pi*t))⁻¹
  ring

/-- The norm of a Gaussian step has exactly the derived radial heat-kernel law. -/
theorem lintegral_step_norm {t : ℝ} (ht : 0<t) (v : Space)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z,F ‖z‖ ∂step t v)=
      ∫⁻ s : ℝ in Ioi 0,ENNReal.ofReal (radialHeat t ‖v‖ s)*F s := by
  have hn : Measurable (fun z : Space => ‖z‖) := by fun_prop
  rw [← lintegral_map hF hn,step_norm_axis,lintegral_map hF hn,step_coordinates ht.le]
  change (∫⁻ z : Space,(F ∘ fun z : Space => ‖z‖) z ∂
    (Measure.pi (fun i : Fin 3 => gaussianReal (axis ‖v‖ i) (⟨t,ht.le⟩ : ℝ≥0))).map (toLp 2)) = _
  rw [lintegral_map (hF.comp hn) (by fun_prop)]
  let variance : ℝ≥0 := ⟨t,ht.le⟩
  change (∫⁻ x : Fin 3 → ℝ,F ‖toLp 2 x‖ ∂Measure.pi
    (fun i : Fin 3 => gaussianReal (axis ‖v‖ i) variance))=_
  have hp := coordinates_preserving (fun i : Fin 3 => gaussianReal (axis ‖v‖ i) variance)
  rw [← hp.symm.map_eq,lintegral_map (by fun_prop) coordinates.symm.measurable]
  change (∫⁻ p : ℝ×(ℝ×ℝ),F ‖toLp 2 (coordinates.symm p)‖ ∂
    (gaussianReal ‖v‖ variance).prod ((gaussianReal 0 variance).prod (gaussianReal 0 variance))) = _
  simp_rw [norm_coordinates]
  have htn : variance≠0 := by
    intro h
    have he := congrArg (fun x : ℝ≥0 => (x:ℝ)) h
    exact ht.ne' he
  rw [gaussianReal_of_var_ne_zero _ htn,gaussianReal_of_var_ne_zero _ htn]
  rw [prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    prod_withDensity (measurable_gaussianPDF _ _) (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply]
  simp_rw [show variance=(⟨t,ht.le⟩ : ℝ≥0) from rfl,heat_gaussianPDF,sub_zero]
  have he (p : ℝ×(ℝ×ℝ)) :
      ENNReal.ofReal (heat t (p.1-‖v‖))*(ENNReal.ofReal (heat t p.2.1)*ENNReal.ofReal (heat t p.2.2))=
      ENNReal.ofReal (heat t (p.1-‖v‖)*heat t p.2.1*heat t p.2.2) := by
    rw [ENNReal.ofReal_mul (mul_nonneg (heat_pos ht _).le (heat_pos ht _).le),
      ENNReal.ofReal_mul (heat_pos ht _).le,mul_assoc]
  simp_rw [he]
  exact lintegral_radial_gaussian ht (norm_nonneg v) F hF

end FKCRT.Radial
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory WithLp
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open SimpleWalk

/-- Lebesgue density supported on strictly positive radii. -/
def transition (t r s : ℝ) : ℝ≥0∞ :=
  (Ioi (0:ℝ)).indicator (fun s => ENNReal.ofReal (radialHeat t r s)) s

lemma measurable_transition : Measurable (fun p : ℝ×ℝ×ℝ => transition p.1 p.2.1 p.2.2) := by
  unfold transition radialHeat killedHeat heat
  apply Measurable.ite (by measurability)
  · apply Measurable.ennreal_ofReal
    apply Measurable.ite (by measurability) <;> fun_prop
  · fun_prop

lemma lintegral_step_transition {t : ℝ} (ht : 0<t) (v : Space)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z,F ‖z‖ ∂step t v)=∫⁻ s,transition t ‖v‖ s*F s := by
  rw [lintegral_step_norm ht v F hF]
  simp only [transition,← indicator_mul_left]
  rw [lintegral_indicator measurableSet_Ioi]

/-- A finite affine Gaussian Markov chain, including a prescribed initial vector. -/
def chain : {m : ℕ} → Space → (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → Space) → Fin m → Space
  | 0,_,_,_,_ => Fin.elim0
  | _m+1,v,a,t,z =>
    let w := a 0 • v+Real.sqrt (t 0) • z 0
    Fin.cons w (chain w (Fin.tail a) (Fin.tail t) (Fin.tail z))

lemma continuous_chain (m : ℕ) (a t : Fin m → ℝ) :
    Continuous (fun p : Space×(Fin m → Space) => chain p.1 a t p.2) := by
  induction m with
  | zero => exact continuous_pi fun i => Fin.elim0 i
  | succ m ih =>
    have hw : Continuous (fun p : Space×(Fin (m+1) → Space) =>
      a 0 • p.1+Real.sqrt (t 0) • p.2 0) := by fun_prop
    have hh := (ih (Fin.tail a) (Fin.tail t)).comp (hw.prodMk
      (show Continuous (fun p : Space×(Fin (m+1) → Space) => Fin.tail p.2) from by fun_prop))
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hw
    · exact (continuous_apply j).comp hh

/-- Joint density, in chronological order, for the radii of that chain. -/
def chainDensity : {m : ℕ} → ℝ → (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ) → ℝ≥0∞
  | 0,_,_,_,_ => 1
  | _m+1,r,a,t,x => transition (t 0) (|a 0| *r) (x 0)*
    chainDensity (x 0) (Fin.tail a) (Fin.tail t) (Fin.tail x)

lemma measurable_chainDensity (m : ℕ) (a t : Fin m → ℝ) :
    Measurable (fun p : ℝ×(Fin m → ℝ) => chainDensity p.1 a t p.2) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    change Measurable (fun p : ℝ×(Fin (m+1) → ℝ) =>
      transition (t 0) (|a 0| * p.1) (p.2 0)*chainDensity (p.2 0) (Fin.tail a) (Fin.tail t) (Fin.tail p.2))
    apply Measurable.mul
    · exact measurable_transition.comp (show Measurable (fun p : ℝ×(Fin (m+1) → ℝ) =>
        (t 0,|a 0| * p.1,p.2 0)) from by fun_prop)
    · exact (ih (Fin.tail a) (Fin.tail t)).comp (show Measurable
        (fun p : ℝ×(Fin (m+1) → ℝ) => (p.2 0,Fin.tail p.2)) from by fun_prop)

/-- Radial integration for every finite affine Gaussian chain, without invoking
an unformalized Bessel process or its transition theorem. -/
theorem lintegral_chain (m : ℕ) (v : Space) (a t : Fin m → ℝ)
    (ht : ∀ i,0<t i) (F : (Fin m → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z,F (fun i => ‖chain v a t z i‖) ∂Measure.pi (fun _ => stdGaussian Space))=
    ∫⁻ x,F x*chainDensity ‖v‖ a t x := by
  induction m generalizing v with
  | zero =>
    have he (x : Fin 0 → ℝ) : F x=F Fin.elim0 := congrArg F (Subsingleton.elim _ _)
    simp only [he,chainDensity,mul_one]
    rw [Measure.pi_of_empty (fun _ : Fin 0 => stdGaussian Space),
      Measure.volume_pi_eq_dirac (α := fun _ : Fin 0 => ℝ)]
    simp
  | succ m ih =>
    let w : Space → Space := fun z => a 0 • v+Real.sqrt (t 0) • z
    let G : ℝ → ℝ≥0∞ := fun r => ∫⁻ x : Fin m → ℝ,
      F (Fin.cons r x)*chainDensity r (Fin.tail a) (Fin.tail t) x
    have hG : Measurable G := by
      apply Measurable.lintegral_prod_right
      exact (hF.comp (by fun_prop)).mul (measurable_chainDensity m (Fin.tail a) (Fin.tail t))
    have hz (z : Space) :
        (∫⁻ zs : Fin m → Space,F (fun i => ‖chain v a t (Fin.cons z zs) i‖)
          ∂Measure.pi (fun _ => stdGaussian Space))=G ‖w z‖ := by
      have hh := ih (w z) (Fin.tail a) (Fin.tail t) (fun i => ht i.succ)
        (fun x => F (Fin.cons ‖w z‖ x)) (hF.comp (by fun_prop))
      convert hh using 1
      congr 1
      funext zs
      congr 1
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hchain : Measurable (fun z => chain v a t z) :=
      ((continuous_chain (m+1) a t).comp (continuous_const.prodMk continuous_id)).measurable
    have hFn : Measurable (fun z => F (fun i => ‖chain v a t z i‖)) :=
      hF.comp (by fun_prop)
    rw [← (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => stdGaussian Space) 0).symm.map_eq]
    rw [lintegral_map hFn (by fun_prop)]
    change (∫⁻ z : Space×(Fin m → Space),F (fun i => ‖chain v a t (Fin.cons z.1 z.2) i‖)
      ∂(stdGaussian Space).prod (Measure.pi (fun _ => stdGaussian Space)))=_
    have hFn' : Measurable (fun z : Space×(Fin m → Space) =>
      F (fun i => ‖chain v a t (Fin.cons z.1 z.2) i‖)) := hFn.comp (by fun_prop)
    rw [lintegral_prod _ hFn'.aemeasurable]
    simp_rw [hz]
    have hw : Measurable w := by fun_prop
    rw [show (∫⁻ z,G ‖w z‖ ∂stdGaussian Space)=(∫⁻ z,G ‖z‖ ∂step (t 0) (a 0 • v)) by
      exact (lintegral_map (hG.comp (by fun_prop)) hw).symm,
      lintegral_step_transition (ht 0) _ G hG,norm_smul,Real.norm_eq_abs]
    have hden : Measurable (fun x => chainDensity ‖v‖ a t x) :=
      (measurable_chainDensity (m+1) a t).comp
        (show Measurable (fun x : Fin (m+1) → ℝ => (‖v‖,x)) from by fun_prop)
    conv_rhs => rw [volume_pi]
    rw [← (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => (volume : Measure ℝ)) 0).symm.map_eq]
    have hfd : Measurable (fun x : Fin (m+1) → ℝ => F x*chainDensity ‖v‖ a t x) := hF.mul hden
    rw [lintegral_map hfd (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm.measurable]
    rw [← volume_pi]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero]
    change (∫⁻ r,transition (t 0) (|a 0| *‖v‖) r*G r)=
      ∫⁻ p : ℝ×(Fin m → ℝ),F (Fin.cons p.1 p.2)*
        (transition (t 0) (|a 0| *‖v‖) p.1*chainDensity p.1 (Fin.tail a) (Fin.tail t) p.2)
        ∂volume.prod volume
    have htden : Measurable (fun p : ℝ×(Fin m → ℝ) =>
      chainDensity p.1 (Fin.tail a) (Fin.tail t) p.2) := measurable_chainDensity m _ _
    have htrans : Measurable (fun r => transition (t 0) (|a 0| * ‖v‖) r) :=
      measurable_transition.comp (show Measurable (fun r : ℝ => (t 0,|a 0| * ‖v‖,r)) from by fun_prop)
    rw [lintegral_prod _ (by fun_prop)]
    apply lintegral_congr
    intro r
    dsimp only [G]
    rw [← lintegral_const_mul _ (by fun_prop)]
    apply lintegral_congr
    intro x
    ring

end FKCRT.Radial
end

end OAI
