import OAI.Probability.GaussianPropeller.OneCell

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace GaussianPropeller.Mills
open OneCell

lemma tail_pos (x : ℝ) : 0 < tail x := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun x => (Real.exp_pos _).le)) density_integrable.integrableOn).mpr
  simp [Function.support, Real.exp_ne_zero]

lemma hasDerivAt_tail (x : ℝ) : HasDerivAt tail (-density x) x := by
  have heq : tail = fun a => tail 0 - ∫ t in (0:ℝ)..a, density t := by
    funext a
    have hi := intervalIntegral.integral_Ioi_sub_Ioi'
      (a := 0) (b := a) density_integrable.integrableOn density_integrable.integrableOn
    change tail 0-tail a = _ at hi
    linarith only [hi]
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right
    (density_integrable.intervalIntegrable)
    (by exact (show StronglyMeasurable density by unfold density; fun_prop).stronglyMeasurableAtFilter) (hasDerivAt_density x).continuousAt).const_sub _

noncomputable def barrier (x : ℝ) : ℝ := (3*x+Real.sqrt (x^2+8))/4
noncomputable def barrier' (x : ℝ) : ℝ := (3+x/Real.sqrt (x^2+8))/4

lemma hasDerivAt_barrier (x : ℝ) : HasDerivAt barrier (barrier' x) x := by
  unfold barrier barrier'
  convert (((hasDerivAt_id x).const_mul 3).add
    (((hasDerivAt_pow 2 x).add_const 8).sqrt (by positivity))).div_const 4 using 1 <;>
    first | rfl | (dsimp; ring)

lemma barrier_pos {x : ℝ} (hx : 0 ≤ x) : 0 < barrier x := by
  unfold barrier
  have : 0 < Real.sqrt (x^2+8) := Real.sqrt_pos.mpr (by positivity)
  positivity

lemma barrier_ge_half {x : ℝ} (hx : 0 ≤ x) : 1/2 ≤ barrier x := by
  have hs := Real.sq_sqrt (show 0 ≤ x^2+8 by positivity)
  have hn := Real.sqrt_nonneg (x^2+8)
  unfold barrier
  nlinarith only [hs,hn,hx,sq_nonneg x]

lemma barrier_differential {x : ℝ} (hx : 0 ≤ x) :
    barrier x ^ 2 - x*barrier x - barrier' x ≤ 0 := by
  let s := Real.sqrt (x^2+8)
  have hs : s^2=x^2+8 := Real.sq_sqrt (by positivity)
  have hp : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hid : (x^2+2)^2*s^2-(x^3+6*x)^2=32 := by rw [hs]; ring
  have hh : x^3+6*x ≤ (x^2+2)*s := by
    have hnon : 0 ≤ x^3+6*x := by positivity
    have hnon' : 0 ≤ (x^2+2)*s := by positivity
    apply (sq_le_sq₀ hnon hnon').mp
    nlinarith only [hid]
  have heq : barrier x^2-x*barrier x-barrier' x =
      (x^3+6*x-(x^2+2)*s)/(8*s) := by
    dsimp [barrier,barrier']
    change ((3*x+s)/4)^2-x*((3*x+s)/4)-(3+x/s)/4 = _
    field_simp [hp.ne']
    have hsm := congrArg (fun t : ℝ => x*t) hs
    have hss := congrArg (fun t : ℝ => s*t) hs
    nlinarith only [hs,hsm,hss]
  rw [heq]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hh) (by positivity)

lemma tail_le_barrier {x : ℝ} (hx : 0 ≤ x) : tail x ≤ density x / barrier x := by
  let f : ℝ → ℝ := fun y => density y/barrier y-tail y
  let f' : ℝ → ℝ := fun y => density y*(barrier y^2-y*barrier y-barrier' y)/barrier y^2
  have hd (y : ℝ) (hy : 0 ≤ y) : HasDerivAt f (f' y) y := by
    convert ((hasDerivAt_density y).div (hasDerivAt_barrier y) (barrier_pos hy).ne').sub
      (hasDerivAt_tail y) using 1
    first | rfl | (dsimp [f']; field_simp [(barrier_pos hy).ne']; ring)
  have hm : AntitoneOn f (Ici 0) := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (barrier_differential (interior_subset hy))) (sq_nonneg _))
  have ht : Tendsto (fun y => density y/barrier y) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (by simpa using tendsto_density.const_mul 2)
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
      exact div_nonneg (Real.exp_pos _).le (barrier_pos hy).le
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
      apply (div_le_iff₀ (barrier_pos hy)).mpr
      have hh := mul_le_mul_of_nonneg_left (barrier_ge_half hy) (Real.exp_pos (-y^2/2)).le
      change density y * (1/2) ≤ density y*barrier y at hh
      nlinarith only [hh]
  have ht' : Tendsto f atTop (𝓝 0) := by
    simpa only [sub_zero, f, tail, id_eq] using ht.sub (tendsto_integral_Ioi_zero (f := density) tendsto_id)
  have hnon : 0 ≤ f x := le_of_tendsto ht' (by
    filter_upwards [eventually_ge_atTop x] with y hy
    exact hm hx (hx.trans hy) hy)
  dsimp [f] at hnon
  linarith only [hnon]

noncomputable def lambda (x : ℝ) : ℝ := density x / tail x
noncomputable def G (x : ℝ) : ℝ := lambda x * (lambda x-x)

lemma lambda_ge_barrier {x : ℝ} (hx : 0 ≤ x) : barrier x ≤ lambda x := by
  rw [lambda, le_div_iff₀ (tail_pos x)]
  have hh := (le_div_iff₀ (barrier_pos hx)).mp (tail_le_barrier hx)
  linarith only [hh]

lemma lambda_pos (x : ℝ) : 0 < lambda x := div_pos (Real.exp_pos _) (tail_pos x)

lemma hasDerivAt_lambda (x : ℝ) : HasDerivAt lambda (lambda x*(lambda x-x)) x := by
  convert (hasDerivAt_density x).div (hasDerivAt_tail x) (tail_pos x).ne' using 1 <;>
    first | rfl | (unfold lambda; field_simp [(tail_pos x).ne']; ring)

lemma hasDerivAt_G (x : ℝ) : HasDerivAt G
    (lambda x*((lambda x-x)*(2*lambda x-x)-1)) x := by
  convert (hasDerivAt_lambda x).mul ((hasDerivAt_lambda x).sub (hasDerivAt_id x)) using 1 <;>
    first | rfl | (dsimp; ring)

lemma G_monotone : MonotoneOn G (Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun x _ => (hasDerivAt_G x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_G x).hasDerivWithinAt)
  intro x hx
  have hx' : 0 ≤ x := interior_subset hx
  apply mul_nonneg (lambda_pos x).le
  have hl := lambda_ge_barrier hx'
  have hs := Real.sq_sqrt (show 0 ≤ x^2+8 by positivity)
  have hp := Real.sqrt_nonneg (x^2+8)
  have hb : x ≤ Real.sqrt (x^2+8) := by nlinarith only [hs,hp,hx']
  have hprod := mul_nonneg (sub_nonneg.mpr hl)
    (show 0 ≤ 2*lambda x+2*barrier x-3*x by unfold barrier at *; linarith only [hl,hb,hx'])
  unfold barrier at hprod
  nlinarith only [hprod,hs]

lemma G_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ G x := by
  apply mul_nonneg (lambda_pos x).le
  have hb := lambda_ge_barrier hx
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ x^2+8 by positivity)
  have hp := Real.sqrt_nonneg (x^2+8)
  have hh : x ≤ Real.sqrt (x^2+8) := by nlinarith only [hs,hp,hx]
  dsimp [barrier] at hb
  linarith only [hb,hh]

lemma G_le_one (x : ℝ) : G x ≤ 1 := by
  have hi : Integrable (fun t : ℝ => (t-lambda x)^2*density t) volume := by
    have hh := (sq_density_integrable.sub (mul_density_integrable.const_mul (2*lambda x))).add
      (density_integrable.const_mul (lambda x^2))
    convert! hh using 1
    ext t
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hz : 0 ≤ ∫ t in Ioi x, (t-lambda x)^2*density t := by
    apply integral_nonneg
    intro t
    exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have heq : (fun t : ℝ => (t-lambda x)^2*density t) =
      fun t => (t^2*density t-2*lambda x*(t*density t))+lambda x^2*density t := by
    funext t
    ring
  rw [heq] at hz
  have h₁ : IntegrableOn (fun t : ℝ => t^2*density t-2*lambda x*(t*density t)) (Ioi x) :=
    (sq_density_integrable.sub (mul_density_integrable.const_mul (2*lambda x))).integrableOn
  have h₂ : IntegrableOn (fun t : ℝ => lambda x^2*density t) (Ioi x) :=
    (density_integrable.const_mul (lambda x^2)).integrableOn
  rw [integral_add h₁ h₂, integral_sub sq_density_integrable.integrableOn
    (show IntegrableOn (fun t : ℝ => 2*lambda x*(t*density t)) (Ioi x) volume from
      (mul_density_integrable.const_mul (2*lambda x)).integrableOn),
    integral_const_mul, integral_const_mul, tail_first_moment, tail_second_moment] at hz
  change 0 ≤ x*density x+tail x-2*lambda x*density x+lambda x^2*tail x at hz
  have he : lambda x*tail x=density x := by
    rw [lambda, div_mul_cancel₀ _ (tail_pos x).ne']
  have ht : tail x*(1-G x) ≥ 0 := by
    dsimp [G]
    nlinarith only [hz,he, congrArg (fun t : ℝ => lambda x*t) he,
      congrArg (fun t : ℝ => x*t) he]
  have h := (mul_nonneg_iff_of_pos_left (tail_pos x)).mp ht
  linarith only [h]

end GaussianPropeller.Mills

end OAI
