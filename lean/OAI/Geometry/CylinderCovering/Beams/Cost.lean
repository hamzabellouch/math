import OAI.Geometry.CylinderCovering.Beams.CostDefinitions

namespace OAI

open MeasureTheory
open scoped Interval

namespace CylinderCovering.BeamCost

theorem inv_sqrt_quadratic {x : ℝ} (hx : |x| ≤ 1/2) :
    |1 / Real.sqrt (1+x) - (1-x/2+3*x^2/8)| ≤ 8*|x|^3 := by
  let y := Real.sqrt (1+x)
  have hxlo : -(1/2:ℝ) ≤ x := (abs_le.mp hx).1
  have hxhi : x ≤ (1/2:ℝ) := (abs_le.mp hx).2
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y^2 = 1+x := Real.sq_sqrt (by linarith)
  have hylo : 1/2 ≤ y := by nlinarith
  have hyhi : y ≤ 3/2 := by nlinarith
  have hypos : 0 < y := by linarith
  have hyne : y ≠ 0 := ne_of_gt hypos
  have hxy : x = (y-1)*(y+1) := by nlinarith
  have habs : |y-1| ≤ |x| := by
    have h := congrArg abs hxy
    rw [abs_mul, abs_of_nonneg (show 0 ≤ y+1 by linarith)] at h
    nlinarith [abs_nonneg (y-1)]
  have hcube : |y-1|^3 ≤ |x|^3 := by gcongr
  have hpoly0 : 0 ≤ 3*y^2+9*y+8 := by positivity
  have hpoly : 3*y^2+9*y+8 ≤ 32 := by nlinarith
  have hid : 8*y*(1/y-(1-x/2+3*x^2/8)) =
      -(y-1)^3*(3*y^2+9*y+8) := by
    rw [hxy]
    field_simp
    ring
  have heq := congrArg abs hid
  rw [abs_mul, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 8 by norm_num),
    abs_of_nonneg hy0, abs_mul, abs_neg, abs_pow, abs_of_nonneg hpoly0] at heq
  have hprod := mul_le_mul hcube hpoly hpoly0 (by positivity : 0 ≤ |x|^3)
  have hleft := mul_le_mul_of_nonneg_right hylo
    (abs_nonneg (1/y-(1-x/2+3*x^2/8)))
  change |1/y-(1-x/2+3*x^2/8)| ≤ 8*|x|^3
  nlinarith

theorem perturbation_expansion {a u v : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1/4) (hu : 0 ≤ u) (hu' : u ≤ a)
    (hv : 0 ≤ v) (hv' : v ≤ a^2) :
    |1/Real.sqrt (1-u+v) - (1+u/2-v/2+3*u^2/8)| ≤ 66*a^3 := by
  have ha2 : a^2 ≤ a := by nlinarith
  have hx : |-u+v| ≤ 2*a := abs_le.mpr ⟨by linarith, by linarith⟩
  have hx' : |-u+v| ≤ 1/2 := by linarith
  have hTaylor := inv_sqrt_quadratic hx'
  have hcube : |-u+v|^3 ≤ (2*a)^3 := by gcongr
  have huv : u*v ≤ a^3 := by
    have h := mul_le_mul hu' hv' hv ha
    nlinarith
  have hv2 : v^2 ≤ a^4 := by
    have h := mul_self_le_mul_self hv hv'
    nlinarith
  have ha4 : a^4 ≤ a^3 := by
    have := mul_nonneg (show 0 ≤ a^3 by positivity) (show 0 ≤ 1-a by linarith)
    nlinarith
  have hquadratic : |(-u+v)^2-u^2| ≤ 3*a^3 := by
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg hu hv, sq_nonneg v]
  have hid : 1/Real.sqrt (1-u+v)-(1+u/2-v/2+3*u^2/8) =
      (1/Real.sqrt (1+(-u+v))-(1-(-u+v)/2+3*(-u+v)^2/8))+
        (3/8)*((-u+v)^2-u^2) := by
    rw [show 1-u+v = 1+(-u+v) by ring]
    ring
  rw [hid]
  have htri := abs_add_le
    (1/Real.sqrt (1+(-u+v))-(1-(-u+v)/2+3*(-u+v)^2/8))
    ((3/8)*((-u+v)^2-u^2))
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/8)] at htri
  nlinarith

theorem ST_bounds {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ S p ∧ S p ≤ 1 ∧ 0 ≤ T p ∧ T p ≤ 1 := by
  have hp2 : p^2 ≤ p := by nlinarith [hp.1, hp.2]
  have hq2 : (1-p)^2 ≤ 1-p := by nlinarith [hp.1, hp.2]
  have hp4 : p^4 ≤ p^2 := by nlinarith [sq_nonneg p, sq_nonneg (1-p), hp.1, hp.2]
  have hq4 : (1-p)^4 ≤ (1-p)^2 := by
    nlinarith [sq_nonneg p, sq_nonneg (1-p), hp.1, hp.2]
  dsimp [S, T]
  exact ⟨by positivity, by linarith, by positivity, by nlinarith⟩

theorem beamDensity_expansion {a p : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/4)
    (hp : p ∈ Set.Icc (0:ℝ) 1) :
    |beamDensity a p -
      (1+a*(2-a)*S p/4+a^2*(2-a)^2*(-T p/8+3*(S p)^2/32))| ≤ 66*a^3 := by
  obtain ⟨hS0, hS1, hT0, hT1⟩ := ST_bounds hp
  have hN : 0 ≤ 2-a := by linarith
  have hN2 : (2-a)^2 ≤ 4 := by nlinarith
  have hu : a*(2-a)*S p/2 ≤ a := by
    have := mul_le_mul_of_nonneg_left hS1 (mul_nonneg ha hN)
    nlinarith [sq_nonneg a]
  have hv : a^2*(2-a)^2*T p/4 ≤ a^2 := by
    have h1 := mul_le_mul_of_nonneg_left hT1 (show 0 ≤ a^2*(2-a)^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hN2 (sq_nonneg a)
    nlinarith
  have h := perturbation_expansion ha ha' (by positivity) hu (by positivity) hv
  convert h using 1
  unfold beamDensity
  congr 1
  ring

theorem integral_S : (∫ p in (0:ℝ)..1, S p) = 2/3 := by
  have heq : S = (fun p : ℝ => 2*p^2-2*p+1) := by funext p; unfold S; ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  · norm_num [integral_pow]
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

theorem integral_T : (∫ p in (0:ℝ)..1, T p) = 2/5 := by
  have heq : T = (fun p : ℝ => 2*p^4-4*p^3+6*p^2-4*p+1) := by
    funext p; unfold T; ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  · norm_num [integral_pow]
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

theorem integral_S_sq : (∫ p in (0:ℝ)..1, (S p)^2) = 7/15 := by
  have heq : (fun p => (S p)^2) =
      (fun p : ℝ => 4*p^4-8*p^3+8*p^2-4*p+1) := by
    funext p; unfold S; ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  · norm_num [integral_pow]
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

theorem integral_beam_taylor (a : ℝ) :
    (∫ p in (0:ℝ)..1,
      (1+a*(2-a)*S p/4+a^2*(2-a)^2*(-T p/8+3*(S p)^2/32))) =
      1+a*(2-a)/6-a^2*(2-a)^2/160 := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add, intervalIntegral.integral_div,
    intervalIntegral.integral_neg, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul]
  · rw [integral_S, integral_T, integral_S_sq, intervalIntegral.integral_const]
    norm_num
    ring
  all_goals
    apply Continuous.intervalIntegrable
    try simp only [S, T]
    fun_prop

theorem beamDensity_continuousOn {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/4) :
    ContinuousOn (beamDensity a) (Set.Icc (0:ℝ) 1) := by
  unfold beamDensity
  apply ContinuousOn.div continuousOn_const
  · apply Continuous.continuousOn
    unfold S T
    fun_prop
  · intro p hp
    apply Real.sqrt_ne_zero'.mpr
    obtain ⟨hS0, hS1, hT0, hT1⟩ := ST_bounds hp
    have hN : 0 ≤ 2-a := by linarith
    have hu := mul_le_mul_of_nonneg_left hS1 (mul_nonneg ha hN)
    have hv : 0 ≤ a^2*(2-a)^2*T p/4 := by positivity
    nlinarith [sq_nonneg a]

theorem beamCost_expansion_N {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/4) :
    |beamCost a - ((2-a)^2+a*(2-a)^3/6-a^2*(2-a)^4/160)| ≤ 264*a^3 := by
  have hbound : ∀ p ∈ Ι (0:ℝ) 1,
      ‖beamDensity a p-(1+a*(2-a)*S p/4+
        a^2*(2-a)^2*(-T p/8+3*(S p)^2/32))‖ ≤ 66*a^3 := by
    intro p hp
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hp
    simpa only [Real.norm_eq_abs] using beamDensity_expansion ha ha' ⟨hp.1.le,hp.2⟩
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [intervalIntegral.integral_sub
    ((beamDensity_continuousOn ha ha').intervalIntegrable_of_Icc (by norm_num))
    (show IntervalIntegrable (fun p => 1+a*(2-a)*S p/4+
        a^2*(2-a)^2*(-T p/8+3*(S p)^2/32)) volume 0 1 from by
      apply Continuous.intervalIntegrable; unfold S T; fun_prop),
    integral_beam_taylor, Real.norm_eq_abs] at hint
  norm_num at hint
  have hN2 : (2-a)^2 ≤ 4 := by nlinarith
  have hprod := mul_le_mul hN2 hint (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 4)
  have hid : beamCost a-((2-a)^2+a*(2-a)^3/6-a^2*(2-a)^4/160) =
      (2-a)^2*((∫ p in (0:ℝ)..1, beamDensity a p)-
        (1+a*(2-a)/6-a^2*(2-a)^2/160)) := by unfold beamCost; ring
  rw [hid, abs_mul, abs_of_nonneg (sq_nonneg _)]
  nlinarith

theorem beamCost_expansion {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/4) :
    |beamCost a-(4-(8/3)*a-(11/10)*a^2)| ≤ 300*a^3 := by
  have hmain := beamCost_expansion_N ha ha'
  have ha2 : a^2 ≤ a := by nlinarith
  have ha3 : a^3 ≤ a^2 := by
    have := mul_nonneg (sq_nonneg a) (show 0 ≤ 1-a by linarith)
    nlinarith
  have hfac : |(6/5:ℝ)-(19/60)*a+a^2/20-a^3/160| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg a, show 0 ≤ a^3 by positivity]
  have herr : |((2-a)^2+a*(2-a)^3/6-a^2*(2-a)^4/160)-
      (4-(8/3)*a-(11/10)*a^2)| ≤ 2*a^3 := by
    have heq : ((2-a)^2+a*(2-a)^3/6-a^2*(2-a)^4/160)-
        (4-(8/3)*a-(11/10)*a^2) =
        a^3*((6/5:ℝ)-(19/60)*a+a^2/20-a^3/160) := by ring
    rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a^3)]
    nlinarith [mul_le_mul_of_nonneg_left hfac (show 0 ≤ a^3 by positivity)]
  have htriangle := abs_add_le
    (beamCost a-((2-a)^2+a*(2-a)^3/6-a^2*(2-a)^4/160))
    (((2-a)^2+a*(2-a)^3/6-a^2*(2-a)^4/160)-(4-(8/3)*a-(11/10)*a^2))
  have hcancel : beamCost a-((2-a)^2+a*(2-a)^3/6-a^2*(2-a)^4/160)+
      (((2-a)^2+a*(2-a)^3/6-a^2*(2-a)^4/160)-(4-(8/3)*a-(11/10)*a^2)) =
      beamCost a-(4-(8/3)*a-(11/10)*a^2) := by ring
  rw [hcancel] at htriangle
  nlinarith [show 0 ≤ a^3 by positivity]

theorem inv_sqrt_loss {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 1-1/Real.sqrt (1+x) ∧ 1-1/Real.sqrt (1+x) ≤ x/2 := by
  let y := Real.sqrt (1+x)
  have hy : 1 ≤ y := by
    dsimp [y]
    exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have hypos : 0 < y := by linarith
  have hy2 : y^2 = 1+x := Real.sq_sqrt (by linarith)
  have hi : 1/y ≤ 1 := (div_le_one hypos).2 hy
  have hlo : 1-x/2 ≤ 1/y := by
    apply (le_div_iff₀ hypos).2
    have hp := mul_nonneg (sq_nonneg (y-1)) (show 0 ≤ y+2 by linarith)
    nlinarith
  change 0 ≤ 1-1/y ∧ 1-1/y ≤ x/2
  constructor <;> linarith

theorem positive_part_padding {x δ : ℝ} (hδ : 0 ≤ δ) :
    |max (x+δ) 0-max x 0| ≤ δ := by
  have hmono : max x 0 ≤ max (x+δ) 0 := max_le_max (by linarith) le_rfl
  have hupper : max (x+δ) 0 ≤ max x 0+δ := by
    apply max_le
    · linarith [le_max_left x 0]
    · linarith [le_max_right x 0]
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
  linarith

theorem stripWidth_bounds {a t : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/100)
    (ht : |t| ≤ 1) : 0 ≤ stripWidth a t ∧ stripWidth a t ≤ 2*a := by
  have ht2 : t^2 ≤ 1 := by nlinarith [abs_le.mp ht, sq_nonneg t]
  have hu2 : (1-|t|)^2 ≤ 1 := by nlinarith [abs_nonneg t]
  have hG : t^2*(1+(1-|t|)^2+t^2) ≤ 3 := by
    have := mul_le_mul ht2 (show 1+(1-|t|)^2+t^2 ≤ 3 by linarith)
      (show 0 ≤ 1+(1-|t|)^2+t^2 by positivity) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith
  have hterm := mul_le_mul_of_nonneg_left hG (sq_nonneg a)
  have ha2 := mul_le_mul_of_nonneg_left ha' ha
  have ha3 := mul_le_mul_of_nonneg_left ha' (sq_nonneg a)
  unfold stripWidth
  refine ⟨le_max_right _ _, max_le ?_ (by positivity)⟩
  nlinarith [mul_nonneg ha (sq_nonneg t)]

theorem stripDensity_width_error {a t : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/100)
    (ht : |t| ≤ 1) : |stripDensity a t-stripWidth a t| ≤ 4*a^3 := by
  obtain ⟨hW0,hW⟩ := stripWidth_bounds ha ha' ht
  have ht3 : |t^3| ≤ 1 := by
    rw [abs_pow]
    calc |t|^3 ≤ (1:ℝ)^3 := by gcongr
         _ = 1 := by norm_num
  have h1 : |a*t| ≤ a := by
    rw [abs_mul, abs_of_nonneg ha]
    nlinarith [mul_le_mul_of_nonneg_left ht ha]
  have h2 : |a^2*t^3| ≤ a^2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
    nlinarith [mul_le_mul_of_nonneg_left ht3 (sq_nonneg a)]
  have hz : |a*t-a^2*t^3| ≤ 2*a := by
    have := abs_sub (a*t) (a^2*t^3)
    have ha2 : a^2 ≤ a := by nlinarith
    linarith
  have hz2 : (a*t-a^2*t^3)^2 ≤ 4*a^2 := by
    have h := mul_self_le_mul_self (abs_nonneg _) hz
    rw [← sq, sq_abs] at h
    nlinarith
  have hLoss := inv_sqrt_loss (sq_nonneg (a*t-a^2*t^3))
  have hprod := mul_le_mul hW hLoss.2 hLoss.1 (show 0 ≤ 2*a by positivity)
  have hid : stripDensity a t-stripWidth a t =
      -(stripWidth a t*(1-1/Real.sqrt (1+(a*t-a^2*t^3)^2))) := by
    unfold stripDensity
    ring
  rw [hid, abs_neg, abs_of_nonneg (mul_nonneg hW0 hLoss.1)]
  nlinarith [mul_le_mul_of_nonneg_left hz2 ha]

theorem beamDensity_physical (a p : ℝ) :
    Real.sqrt 2 / Real.sqrt
      (1+((1-a*(2-a)*p^2)^2+(-1+a*(2-a)*(1-p)^2)^2)/2) = beamDensity a p := by
  have hden : 1+((1-a*(2-a)*p^2)^2+(-1+a*(2-a)*(1-p)^2)^2)/2 =
      2*(1-a*(2-a)*S p/2+a^2*(2-a)^2*T p/4) := by
    unfold S T
    ring
  rw [hden, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), div_mul_eq_div_div,
    div_self (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2))]
  rfl

theorem cutoff_bounds : (1/2:ℝ) ≤ cutoff ∧ cutoff ≤ 3/4 ∧ cutoff^2 = 1/2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  unfold cutoff
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem cutoff_eq_inv_sqrt : cutoff = 1/Real.sqrt 2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)
  unfold cutoff
  apply (eq_div_iff (ne_of_gt hp)).2
  nlinarith

theorem strip_quadratic_bounds {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ t^2*(1+(1-t)^2+t^2) ∧ t^2*(1+(1-t)^2+t^2) ≤ 3 := by
  have ht2 : t^2 ≤ 1 := by nlinarith [ht.1,ht.2]
  have hu2 : (1-t)^2 ≤ 1 := by nlinarith [ht.1,ht.2]
  refine ⟨by positivity, ?_⟩
  have h := mul_le_mul ht2 (show 1+(1-t)^2+t^2 ≤ 3 by linarith)
    (show 0 ≤ 1+(1-t)^2+t^2 by positivity) (by norm_num : (0:ℝ) ≤ 1)
  nlinarith

theorem stripPolynomial_nonneg {a t : ℝ} (ha : 0 ≤ a)
    (ht : t ∈ Set.Icc 0 cutoff) : 0 ≤ stripPolynomial a t := by
  have hR := cutoff_bounds
  have ht2 : t^2 ≤ 1/2 := by
    have h := mul_self_le_mul_self ht.1 ht.2
    nlinarith
  unfold stripPolynomial
  exact add_nonneg (mul_nonneg ha (by linarith)) (by positivity)

theorem stripPolynomial_nonpos {a t : ℝ} (ha : 0 ≤ a)
    (ht : t ∈ Set.Icc (cutoff+4*a) 1) : stripPolynomial a t ≤ 0 := by
  have hR := cutoff_bounds
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hG := (strip_quadratic_bounds ⟨ht0,ht.2⟩).2
  have hprod : 4*a ≤ (t-cutoff)*(t+cutoff) := by
    have h := mul_le_mul (show 4*a ≤ t-cutoff by linarith [ht.1])
      (show (1:ℝ) ≤ t+cutoff by linarith [ht.1]) (by norm_num : (0:ℝ) ≤ 1)
      (show 0 ≤ t-cutoff by linarith [ht.1])
    simpa using h
  have ht2 : 1/2+4*a ≤ t^2 := by nlinarith [hR.2.2]
  have hlead := mul_le_mul_of_nonneg_left ht2 ha
  have hquad := mul_le_mul_of_nonneg_left hG (sq_nonneg a)
  unfold stripPolynomial
  nlinarith [sq_nonneg a]

theorem stripPolynomial_collar_bound {a t : ℝ} (ha : 0 ≤ a)
    (ht : t ∈ Set.Icc cutoff 1) :
    0 ≤ max (stripPolynomial a t) 0 ∧ max (stripPolynomial a t) 0 ≤ 3*a^2 := by
  have hR := cutoff_bounds
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hG := (strip_quadratic_bounds ⟨ht0,ht.2⟩).2
  have ht2 : 1/2 ≤ t^2 := by
    have h := mul_self_le_mul_self (show 0 ≤ cutoff by linarith) ht.1
    nlinarith [hR.2.2]
  have hlead := mul_nonpos_of_nonneg_of_nonpos ha (show 1-2*t^2 ≤ 0 by linarith)
  have hquad := mul_le_mul_of_nonneg_left hG (sq_nonneg a)
  refine ⟨le_max_right _ _, max_le ?_ (by positivity)⟩
  unfold stripPolynomial
  nlinarith

theorem stripDensity_core_error {a t : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/100)
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |stripDensity a t-max (stripPolynomial a t) 0| ≤ 29*a^3 := by
  have htAbs : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hden := stripDensity_width_error ha ha' htAbs
  have hpad := positive_part_padding (x := stripPolynomial a t)
    (show 0 ≤ 25*a^3 by positivity)
  have hW : stripWidth a t = max (stripPolynomial a t+25*a^3) 0 := by
    unfold stripWidth stripPolynomial
    rw [abs_of_nonneg ht.1]
  rw [← hW] at hpad
  have htri := abs_add_le (stripDensity a t-stripWidth a t)
    (stripWidth a t-max (stripPolynomial a t) 0)
  have hid : (stripDensity a t-stripWidth a t)+
      (stripWidth a t-max (stripPolynomial a t) 0) =
      stripDensity a t-max (stripPolynomial a t) 0 := by ring
  rw [hid] at htri
  linarith

theorem positive_part_integral_error {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/100) :
    |(∫ t in (0:ℝ)..1, max (stripPolynomial a t) 0)-
      (∫ t in (0:ℝ)..cutoff, stripPolynomial a t)| ≤ 12*a^3 := by
  have hR := cutoff_bounds
  have h0R : 0 ≤ cutoff := by linarith
  have hRc : cutoff ≤ cutoff+4*a := by linarith
  have hc1 : cutoff+4*a ≤ 1 := by linarith
  have hf : Continuous (fun t => max (stripPolynomial a t) 0) := by
    unfold stripPolynomial; fun_prop
  have hbelow : (∫ t in (0:ℝ)..cutoff, max (stripPolynomial a t) 0) =
      ∫ t in (0:ℝ)..cutoff, stripPolynomial a t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le h0R] at ht
    exact max_eq_left (stripPolynomial_nonneg ha ht)
  have habove : (∫ t in (cutoff+4*a)..1, max (stripPolynomial a t) 0) = 0 := by
    calc
      (∫ t in (cutoff+4*a)..1, max (stripPolynomial a t) 0) =
          ∫ _t in (cutoff+4*a)..1, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hc1] at ht
        exact max_eq_right (stripPolynomial_nonpos ha ht)
      _ = 0 := by simp
  have hsplit : (∫ t in (0:ℝ)..1, max (stripPolynomial a t) 0) =
      (∫ t in (0:ℝ)..cutoff, max (stripPolynomial a t) 0)+
      (∫ t in cutoff..(cutoff+4*a), max (stripPolynomial a t) 0) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 (cutoff+4*a)) (hf.intervalIntegrable (cutoff+4*a) 1),
      habove, add_zero,
      ← intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable 0 cutoff) (hf.intervalIntegrable cutoff (cutoff+4*a))]
  have hbound : ∀ t ∈ Ι cutoff (cutoff+4*a),
      ‖max (stripPolynomial a t) 0‖ ≤ 3*a^2 := by
    intro t ht
    rw [Set.uIoc_of_le hRc] at ht
    obtain ⟨h0,h1⟩ := stripPolynomial_collar_bound ha ⟨ht.1.le,ht.2.trans hc1⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hRc)] at hint
  rw [hsplit, hbelow]
  have hid : (∫ t in (0:ℝ)..cutoff, stripPolynomial a t)+
      (∫ t in cutoff..(cutoff+4*a), max (stripPolynomial a t) 0)-
      (∫ t in (0:ℝ)..cutoff, stripPolynomial a t) =
      ∫ t in cutoff..(cutoff+4*a), max (stripPolynomial a t) 0 := by ring
  rw [hid]
  nlinarith

theorem continuous_stripDensity (a : ℝ) : Continuous (stripDensity a) := by
  unfold stripDensity
  apply Continuous.div
  · unfold stripWidth; fun_prop
  · fun_prop
  · intro t
    exact Real.sqrt_ne_zero'.mpr (by positivity)

theorem strip_half_integral_error {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/100) :
    |(∫ t in (0:ℝ)..1, stripDensity a t)-
      (∫ t in (0:ℝ)..cutoff, stripPolynomial a t)| ≤ 41*a^3 := by
  have hbound : ∀ t ∈ Ι (0:ℝ) 1,
      ‖stripDensity a t-max (stripPolynomial a t) 0‖ ≤ 29*a^3 := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    simpa only [Real.norm_eq_abs] using stripDensity_core_error ha ha' ⟨ht.1.le,ht.2⟩
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [intervalIntegral.integral_sub ((continuous_stripDensity a).intervalIntegrable _ _)
    (show IntervalIntegrable (fun t => max (stripPolynomial a t) 0) volume 0 1 from by
      apply Continuous.intervalIntegrable; unfold stripPolynomial; fun_prop),
    Real.norm_eq_abs] at hint
  norm_num at hint
  have hcollar := positive_part_integral_error ha ha'
  have htriangle := abs_add_le
    ((∫ t in (0:ℝ)..1, stripDensity a t)-(∫ t in (0:ℝ)..1, max (stripPolynomial a t) 0))
    ((∫ t in (0:ℝ)..1, max (stripPolynomial a t) 0)-
      (∫ t in (0:ℝ)..cutoff, stripPolynomial a t))
  have hid : ((∫ t in (0:ℝ)..1, stripDensity a t)-(∫ t in (0:ℝ)..1, max (stripPolynomial a t) 0))+
      ((∫ t in (0:ℝ)..1, max (stripPolynomial a t) 0)-
      (∫ t in (0:ℝ)..cutoff, stripPolynomial a t)) =
      (∫ t in (0:ℝ)..1, stripDensity a t)-
      (∫ t in (0:ℝ)..cutoff, stripPolynomial a t) := by ring
  rw [hid] at htriangle
  linarith

theorem stripDensity_even (a t : ℝ) : stripDensity a (-t) = stripDensity a t := by
  have hnum : stripWidth a (-t) = stripWidth a t := by
    unfold stripWidth
    simp only [neg_sq, abs_neg]
  have hden : (a*(-t)-a^2*(-t)^3)^2 = (a*t-a^2*t^3)^2 := by ring
  unfold stripDensity
  rw [hnum,hden]

theorem stripCost_half (a : ℝ) :
    stripCost a = 4*Real.sqrt 2*(∫ t in (0:ℝ)..1, stripDensity a t) := by
  have hneg := intervalIntegral.integral_comp_neg (a := (-1:ℝ)) (b := 0)
    (stripDensity a)
  simp only [stripDensity_even, neg_zero, neg_neg] at hneg
  unfold stripCost
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((continuous_stripDensity a).intervalIntegrable (-1) 0)
    ((continuous_stripDensity a).intervalIntegrable 0 1), hneg]
  ring

theorem integral_stripPolynomial (a : ℝ) :
    (∫ t in (0:ℝ)..cutoff, stripPolynomial a t) =
      a*cutoff+(-2*a+2*a^2)*cutoff^3/3-a^2*cutoff^4/2+2*a^2*cutoff^5/5 := by
  have heq : stripPolynomial a =
      (fun t : ℝ => a+(-2*a+2*a^2)*t^2-2*a^2*t^3+2*a^2*t^4) := by
    funext t; unfold stripPolynomial; ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  · norm_num [integral_pow, intervalIntegral.integral_const]
    ring
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

theorem stripPolynomial_cost (a : ℝ) :
    4*Real.sqrt 2*(∫ t in (0:ℝ)..cutoff, stripPolynomial a t) =
      (8/3)*a+((26/15)-Real.sqrt 2/2)*a^2 := by
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs4 : (Real.sqrt 2)^4 = 4 := by
    calc (Real.sqrt 2)^4 = ((Real.sqrt 2)^2)^2 := by ring
         _ = 4 := by rw [hs2]; norm_num
  have hs5 : (Real.sqrt 2)^5 = 4*Real.sqrt 2 := by rw [pow_succ, hs4]
  have hs6 : (Real.sqrt 2)^6 = 8 := by
    calc (Real.sqrt 2)^6 = ((Real.sqrt 2)^2)^3 := by ring
         _ = 8 := by rw [hs2]; norm_num
  rw [integral_stripPolynomial]
  unfold cutoff
  ring_nf
  rw [hs2, hs4, hs5, hs6]
  ring

theorem stripCost_expansion {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/100) :
    |stripCost a-((8/3)*a+((26/15)-Real.sqrt 2/2)*a^2)| ≤ 300*a^3 := by
  have h := strip_half_integral_error ha ha'
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs : Real.sqrt 2 ≤ 3/2 := by nlinarith
  rw [stripCost_half, ← stripPolynomial_cost]
  rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ 4*Real.sqrt 2 by positivity)]
  have hprod := mul_le_mul (show 4*Real.sqrt 2 ≤ 6 by linarith) h (abs_nonneg _)
    (by norm_num : (0:ℝ) ≤ 6)
  nlinarith [show 0 ≤ a^3 by positivity]

theorem totalCost_expansion {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/100) :
    |beamCost a+stripCost a-(4+((19/30)-Real.sqrt 2/2)*a^2)| ≤ 600*a^3 := by
  have h1 := beamCost_expansion ha (show a ≤ 1/4 by linarith)
  have h2 := stripCost_expansion ha ha'
  have htri := abs_add_le
    (beamCost a-(4-(8/3)*a-(11/10)*a^2))
    (stripCost a-((8/3)*a+((26/15)-Real.sqrt 2/2)*a^2))
  have hid : (beamCost a-(4-(8/3)*a-(11/10)*a^2))+
      (stripCost a-((8/3)*a+((26/15)-Real.sqrt 2/2)*a^2)) =
      beamCost a+stripCost a-(4+((19/30)-Real.sqrt 2/2)*a^2) := by ring
  rw [hid] at htri
  linarith

theorem gain_coefficient_bound : (19/30:ℝ)-Real.sqrt 2/2 ≤ -1/20 := by
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  nlinarith

theorem totalCost_saving {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/20000) :
    beamCost a+stripCost a ≤ 4-a^2/50 := by
  have hexp := (abs_le.mp (totalCost_expansion ha (show a ≤ 1/100 by linarith))).2
  have hcoef := mul_le_mul_of_nonneg_right gain_coefficient_bound (sq_nonneg a)
  have hcube := mul_le_mul_of_nonneg_right ha' (sq_nonneg a)
  nlinarith

theorem totalCost_lt_four {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1/20000) :
    beamCost a+stripCost a < 4 := by
  have h := totalCost_saving ha.le ha'
  nlinarith [sq_pos_of_pos ha]

theorem exists_strict_gain : ∃ a : ℝ, 0 < a ∧ a < 1/2 ∧ beamCost a+stripCost a < 4 := by
  refine ⟨1/20000, by norm_num, by norm_num, ?_⟩
  exact totalCost_lt_four (by norm_num) le_rfl

theorem fullCost : CostStatement :=
  ⟨fun _ => beamCost_expansion, fun _ => stripCost_expansion,
    fun _ => totalCost_expansion, fun _ => totalCost_lt_four⟩

end CylinderCovering.BeamCost

end OAI
