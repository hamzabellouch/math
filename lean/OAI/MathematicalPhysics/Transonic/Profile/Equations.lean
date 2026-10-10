import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace OAI

/-!
# Relativistic self-similar profile equations

The sonic change of variables and compatibility conditions for the septic wave
profile, following the relativistic profile construction of Buckmaster and Chen.
-/

section

noncomputable section
open scoped ContDiff
namespace SepticProfile

def velocityToU (y v : ℝ) : ℝ := (y - v) / (1 - y * v)

def profileDenom (ell y v : ℝ) : ℝ :=
  y * ((1 - y * v)^2 - ell * (v - y)^2)

def profileNumer (ell beta y v : ℝ) : ℝ :=
  (1 - v^2) * (beta * ell * (1 - v^2) * y - 3 * v * (1 - y * v))

def sonicDenom (ell y U : ℝ) : ℝ := y * (1-y^2) * (1-ell*U^2)

def sonicNumer (ell beta y U : ℝ) : ℝ :=
  (1-U^2) * (y*(1-beta)*(1-ell*U^2) + 3*(y-U) - beta*(ell-1)*y)

theorem hasDerivAt_velocityToU {v : ℝ → ℝ} {y v' : ℝ}
    (hv : HasDerivAt v v' y) (hden : 1 - y*v y ≠ 0) :
    HasDerivAt (fun x => velocityToU x (v x))
      ((1 - (v y)^2 - (1-y^2)*v') / (1-y*v y)^2) y := by
  change HasDerivAt (fun x => (x - v x) / (1 - x*v x)) _ y
  convert ((hasDerivAt_id y).fun_sub hv).fun_div
    ((hasDerivAt_const y (1 : ℝ)).fun_sub ((hasDerivAt_id y).fun_mul hv)) hden using 1 <;> first | rfl | (simp only [id_eq]; ring)

theorem transformed_profile_equation {ell beta y v v' : ℝ}
    (hden : 1-y*v ≠ 0)
    (hode : profileDenom ell y v * v' = profileNumer ell beta y v) :
    sonicDenom ell y (velocityToU y v) *
      ((1-v^2-(1-y^2)*v')/(1-y*v)^2) =
    sonicNumer ell beta y (velocityToU y v) := by
  dsimp [profileDenom, profileNumer] at hode
  dsimp [sonicDenom, sonicNumer, velocityToU]
  field_simp
  linear_combination -(1-y^2)^2 * hode

theorem sonicDenom_at_sonic {ell c y : ℝ} (hc : ell*c^2 = 1) :
    sonicDenom ell y c = 0 := by
  simp [sonicDenom, hc]

theorem sonicNumer_at_sonic {ell beta c y : ℝ} (hc : ell*c^2 = 1) :
    sonicNumer ell beta y c =
      (1-c^2) * ((3-beta*(ell-1))*y-3*c) := by
  simp only [sonicNumer, hc, sub_self, mul_zero, zero_add]
  ring

theorem sonic_radius_necessary {ell beta c y m : ℝ}
    (hc : ell*c^2 = 1) (hcunit : 1-c^2 ≠ 0)
    (hbeta : 3-beta*(ell-1) ≠ 0)
    (hode : sonicDenom ell y c * m = sonicNumer ell beta y c) :
    y = 3*c / (3-beta*(ell-1)) := by
  rw [sonicDenom_at_sonic hc, zero_mul, sonicNumer_at_sonic hc] at hode
  have hzero : (3-beta*(ell-1))*y-3*c = 0 :=
    (mul_eq_zero.mp hode.symm).resolve_left hcunit
  apply (eq_div_iff hbeta).2
  nlinarith only [hzero]

theorem sonic_no_slope_off_selected_radius {ell beta c y : ℝ}
    (hc : ell*c^2 = 1) (hcunit : 1-c^2 ≠ 0)
    (hbeta : 3-beta*(ell-1) ≠ 0)
    (hy : y ≠ 3*c / (3-beta*(ell-1))) :
    ¬ ∃ m : ℝ, sonicDenom ell y c * m = sonicNumer ell beta y c := by
  rintro ⟨m, hm⟩
  exact hy (sonic_radius_necessary hc hcunit hbeta hm)

theorem no_rhs_on_sonic_neighborhood {ell beta c eps : ℝ}
    (hc : ell*c^2 = 1) (hcunit : 1-c^2 ≠ 0)
    (hbeta : 3-beta*(ell-1) ≠ 0) (heps : 0 < eps) :
    ¬ ∃ F : ℝ → ℝ, ∀ y : ℝ,
      |y - 3*c/(3-beta*(ell-1))| < eps →
      sonicDenom ell y c * F y = sonicNumer ell beta y c := by
  rintro ⟨F, hF⟩
  let a := 3*c/(3-beta*(ell-1))
  have hnear : |(a + eps/2)-a| < eps := by
    rw [add_sub_cancel_left, abs_of_pos (by positivity : 0 < eps/2)]
    linarith
  have hne : a + eps/2 ≠ a := by linarith
  exact sonic_no_slope_off_selected_radius hc hcunit hbeta hne
    ⟨F (a+eps/2), hF _ hnear⟩

theorem hasDerivAt_sonicDenom {ell y m : ℝ} {U : ℝ → ℝ}
    (hU : HasDerivAt U m y) :
    HasDerivAt (fun x => sonicDenom ell x (U x))
      ((1-3*y^2)*(1-ell*(U y)^2)-2*ell*y*(1-y^2)*(U y)*m) y := by
  change HasDerivAt (fun x => x*(1-x^2)*(1-ell*(U x)^2)) _ y
  convert ((hasDerivAt_id y).fun_mul (((hasDerivAt_id y).pow 2).const_sub 1)).fun_mul
    (((hU.pow 2).const_mul ell).const_sub 1) using 1 <;>
    first | rfl | (simp only [Pi.pow_apply, id_eq]; ring)

theorem hasDerivAt_sonicNumer {ell beta y m : ℝ} {U : ℝ → ℝ}
    (hU : HasDerivAt U m y) :
    HasDerivAt (fun x => sonicNumer ell beta x (U x))
      (-2*(U y)*m *
          (y*(1-beta)*(1-ell*(U y)^2)+3*(y-U y)-beta*(ell-1)*y) +
        (1-(U y)^2) * ((1-beta)*(1-ell*(U y)^2) -
          2*ell*y*(1-beta)*(U y)*m+3*(1-m)-beta*(ell-1))) y := by
  change HasDerivAt (fun x => (1-(U x)^2) *
    (x*(1-beta)*(1-ell*(U x)^2)+3*(x-U x)-beta*(ell-1)*x)) _ y
  have hid := hasDerivAt_id y
  convert ((hU.pow 2).const_sub 1).fun_mul
    ((((hid.mul_const (1-beta)).fun_mul (((hU.pow 2).const_mul ell).const_sub 1)).fun_add
        ((hid.fun_sub hU).const_mul 3)).fun_sub (hid.const_mul (beta*(ell-1))))
      using 1 <;> first | rfl | (simp only [Pi.pow_apply, id_eq]; ring)

theorem sonic_crossing_slope_equation {ell beta c y m m₂ : ℝ} {U : ℝ → ℝ}
    (hU : HasDerivAt U m y) (hU₂ : HasDerivAt (deriv U) m₂ y)
    (hvalue : U y = c) (hc : ell*c^2 = 1) (hcunit : 1-c^2 ≠ 0)
    (hode : ∀ᶠ x in nhds y,
      sonicDenom ell x (U x) * deriv U x = sonicNumer ell beta x (U x)) :
    2*ell*c*y*(1-y^2)*m^2 -
      (1-c^2)*(3+2*ell*c*y*(1-beta))*m +
      (1-c^2)*(3-beta*(ell-1)) = 0 := by
  have hat := hode.self_of_nhds
  rw [hvalue, sonicDenom_at_sonic hc, zero_mul] at hat
  have hcompat : 3*(y-c)-beta*(ell-1)*y = 0 := by
    have hz : (1-c^2)*(3*(y-c)-beta*(ell-1)*y) = 0 := by
      simpa [sonicNumer, hc] using hat.symm
    exact (mul_eq_zero.mp hz).resolve_left hcunit
  have hd := ((hasDerivAt_sonicDenom hU).fun_mul hU₂).congr_of_eventuallyEq (Filter.EventuallyEq.symm hode)
  have heq := hd.unique (hasDerivAt_sonicNumer hU)
  simp only [hU.deriv, hvalue, sonicDenom_at_sonic hc, hc, sub_self,
    mul_zero, zero_mul, zero_add, add_zero, hcompat] at heq
  linear_combination -heq

theorem transformed_equation_of_source {ell beta y v' : ℝ} {v : ℝ → ℝ}
    (hv : HasDerivAt v v' y) (hden : 1-y*v y ≠ 0)
    (hode : profileDenom ell y (v y) * deriv v y = profileNumer ell beta y (v y)) :
    sonicDenom ell y (velocityToU y (v y)) *
      deriv (fun x => velocityToU x (v x)) y =
      sonicNumer ell beta y (velocityToU y (v y)) := by
  rw [(hasDerivAt_velocityToU hv hden).deriv]
  exact transformed_profile_equation hden (by simpa only [hv.deriv] using hode)

theorem no_finite_sonic_rhs_limit {ell beta c y : ℝ}
    (hc : ell*c^2 = 1) (hcunit : 1-c^2 ≠ 0)
    (hbeta : 3-beta*(ell-1) ≠ 0)
    (hy : y ≠ 3*c/(3-beta*(ell-1))) :
    ¬ ∃ F : ℝ → ℝ, ContinuousAt F c ∧
      ∀ᶠ z in nhdsWithin c (Set.Ioi c),
        sonicDenom ell y z * F z = sonicNumer ell beta y z := by
  rintro ⟨F, hF, hEq⟩
  have hD : ContinuousAt (fun z : ℝ => sonicDenom ell y z) c := by
    unfold sonicDenom
    fun_prop
  have hN : ContinuousAt (fun z : ℝ => sonicNumer ell beta y z) c := by
    unfold sonicNumer
    fun_prop
  have hzero : Filter.Tendsto (fun z => sonicDenom ell y z * F z)
      (nhdsWithin c (Set.Ioi c)) (nhds 0) := by
    have hz := (hD.mul hF).tendsto
    change Filter.Tendsto (fun z => sonicDenom ell y z * F z)
      (nhds c) (nhds (sonicDenom ell y c * F c)) at hz
    rw [sonicDenom_at_sonic hc, zero_mul] at hz
    exact hz.mono_left nhdsWithin_le_nhds
  have heqzero : sonicNumer ell beta y c = 0 :=
    tendsto_nhds_unique (hN.tendsto.mono_left nhdsWithin_le_nhds)
      (hzero.congr' hEq)
  exact sonic_no_slope_off_selected_radius hc hcunit hbeta hy
    ⟨0, by rw [mul_zero, heqzero]⟩

theorem not_continuousAt_sonic_quotient {ell beta c y : ℝ}
    (hc : ell*c^2 = 1) (hcpos : 0 < c) (hcunit : 1-c^2 ≠ 0)
    (hbeta : 3-beta*(ell-1) ≠ 0)
    (hypos : 0 < y) (hylt : y < 1)
    (hy : y ≠ 3*c/(3-beta*(ell-1))) :
    ¬ ContinuousAt (fun z => sonicNumer ell beta y z / sonicDenom ell y z) c := by
  intro hcont
  apply no_finite_sonic_rhs_limit hc hcunit hbeta hy
  refine ⟨_, hcont, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hcz : c < z := hz
  have hzsq : c^2 < z^2 := by nlinarith
  have hell : 0 < ell := by
    by_contra! he
    have := mul_nonpos_of_nonpos_of_nonneg he (sq_nonneg c)
    linarith
  have hlast : 1-ell*z^2 ≠ 0 := by
    have hmul := mul_lt_mul_of_pos_left hzsq hell
    intro hh
    nlinarith only [hc, hmul, hh]
  have hyunit : 1-y^2 ≠ 0 := by nlinarith
  have hden : sonicDenom ell y z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ne_of_gt hypos) hyunit) hlast
  field_simp

theorem axis_slope_necessary {ell beta m m₂ : ℝ} {v : ℝ → ℝ}
    (hv : HasDerivAt v m 0) (hv₂ : HasDerivAt (deriv v) m₂ 0)
    (hvzero : v 0 = 0)
    (hode : ∀ᶠ y in nhdsWithin 0 (Set.Ici 0),
      profileDenom ell y (v y) * deriv v y = profileNumer ell beta y (v y)) :
    m = beta*ell/4 := by
  have hid := hasDerivAt_id (0 : ℝ)
  have hQ := (((hid.fun_mul hv).const_sub 1).pow 2).fun_sub
    (((hv.fun_sub hid).pow 2).const_mul ell)
  have hD : HasDerivAt (fun y => profileDenom ell y (v y)) 1 0 := by
    convert hid.fun_mul hQ using 1 <;>
      first | rfl | simp [hvzero, id_eq]
  have hL : HasDerivAt (fun y => profileDenom ell y (v y) * deriv v y) m 0 := by
    convert hD.fun_mul hv₂ using 1 ;
      first | rfl | simp [profileDenom, hvzero, hv.deriv]
  have hN : HasDerivAt (fun y => profileNumer ell beta y (v y))
      (beta*ell-3*m) 0 := by
    convert ((hv.pow 2).const_sub 1).fun_mul
      (((((hv.pow 2).const_sub 1).const_mul (beta*ell)).fun_mul hid).fun_sub
        ((hv.const_mul 3).fun_mul ((hid.fun_mul hv).const_sub 1))) using 1 <;>
      first | rfl | simp [hvzero, id_eq]
  have heq : m = beta*ell-3*m := by
    calc
      m = derivWithin (fun y => profileDenom ell y (v y) * deriv v y)
          (Set.Ici 0) 0 :=
        (hL.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)).symm
      _ = derivWithin (fun y => profileNumer ell beta y (v y)) (Set.Ici 0) 0 :=
        Filter.EventuallyEq.derivWithin_eq_of_mem hode (by simp)
      _ = beta*ell-3*m := hN.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)
  linarith

theorem radial_velocity_contDiff {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Set.Ici 0)) :
    ContDiff ℝ ∞ (fun y : ℝ => y*g (y^2)) := by
  exact contDiff_id.mul (hg.comp_contDiff (contDiff_id.pow 2) (fun y => sq_nonneg y))

theorem source_axis_slope {ell beta : ℝ} {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Set.Ici 0))
    (hode : ∀ y : ℝ, 0 ≤ y →
      profileDenom ell y (y*g (y^2)) * deriv (fun x : ℝ => x*g (x^2)) y =
        profileNumer ell beta y (y*g (y^2))) :
    deriv (fun y : ℝ => y*g (y^2)) 0 = beta*ell/4 := by
  let v : ℝ → ℝ := fun y => y*g (y^2)
  have hcv : ContDiff ℝ ∞ v := radial_velocity_contDiff hg
  have hcdv : ContDiff ℝ ∞ (deriv v) := (contDiff_infty_iff_deriv.mp hcv).2
  apply axis_slope_necessary
    ((hcv.differentiable (by simp) 0).hasDerivAt)
    ((hcdv.differentiable (by simp) 0).hasDerivAt) (by simp [v])
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hode y hy

def ell : ℝ := 5/3
def sonicSpeed : ℝ := 1 / Real.sqrt ell
def sonicRadius (beta : ℝ) : ℝ := 3 / (Real.sqrt ell * (3-beta*(ell-1)))

theorem source_parameter_bounds {beta : ℝ}
    (hbeta : 1 < beta) (hupper : beta*(ell+Real.sqrt ell) < 3) :
    ell*sonicSpeed^2 = 1 ∧ 0 < sonicSpeed ∧ 1-sonicSpeed^2 ≠ 0 ∧
    0 < 3-beta*(ell-1) ∧ 0 < sonicRadius beta ∧ sonicRadius beta < 1 ∧
    0 < beta*ell/4 ∧ beta*ell/4 < 1 := by
  have hell : (0 : ℝ) < ell := by norm_num [ell]
  have hrpos : 0 < Real.sqrt ell := Real.sqrt_pos.2 hell
  have hrne : Real.sqrt ell ≠ 0 := ne_of_gt hrpos
  have hrsq : (Real.sqrt ell)^2 = ell := Real.sq_sqrt (le_of_lt hell)
  have hrgt : 1 < Real.sqrt ell := by
    have helgt : (1 : ℝ) < ell := by norm_num [ell]
    nlinarith only [hrsq, hrpos, helgt]
  have hcpos : 0 < sonicSpeed := by exact div_pos (by norm_num) hrpos
  have hclt : sonicSpeed < 1 := by
    dsimp [sonicSpeed]
    exact (div_lt_one hrpos).2 hrgt
  have hcsq : ell*sonicSpeed^2 = 1 := by
    dsimp [sonicSpeed]
    field_simp
    exact hrsq.symm
  have halg : (ell+Real.sqrt ell)*(1-sonicSpeed) = ell-1 := by
    dsimp [sonicSpeed]
    field_simp
    nlinarith only [hrsq]
  have hlow : 3*sonicSpeed < 3-beta*(ell-1) := by
    have hm := mul_lt_mul_of_pos_right hupper (sub_pos.2 hclt)
    rw [mul_assoc, halg] at hm
    linarith
  have hqpos : 0 < 3-beta*(ell-1) := by linarith
  have harad : sonicRadius beta = 3*sonicSpeed/(3-beta*(ell-1)) := by
    dsimp [sonicRadius, sonicSpeed]
    field_simp
  refine ⟨hcsq, hcpos, ?_, hqpos, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · rw [harad]
    exact div_pos (by positivity) hqpos
  · rw [harad]
    exact (div_lt_one hqpos).2 hlow
  · positivity
  · have hbr := mul_pos (show 0 < beta by linarith) hrpos
    nlinarith only [hupper, hbr]

theorem source_no_rhs_on_sonic_neighborhood {beta eps : ℝ}
    (hbeta : 1 < beta) (hupper : beta*(ell+Real.sqrt ell) < 3) (heps : 0 < eps) :
    ¬ ∃ F : ℝ → ℝ, ∀ y : ℝ, |y-sonicRadius beta| < eps →
      sonicDenom ell y sonicSpeed * F y = sonicNumer ell beta y sonicSpeed := by
  obtain ⟨hc, _, hcunit, hq, _⟩ := source_parameter_bounds hbeta hupper
  have harad : sonicRadius beta = 3*sonicSpeed/(3-beta*(ell-1)) := by
    simp only [sonicRadius, sonicSpeed, div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [harad] using
    no_rhs_on_sonic_neighborhood hc hcunit (ne_of_gt hq) heps

def q (beta : ℝ) : ℝ := 3 - beta * (ell - 1)

def slopeA (beta : ℝ) : ℝ :=
  2 * ell * sonicSpeed * sonicRadius beta * (1 - (sonicRadius beta)^2)

def slopeB (beta : ℝ) : ℝ :=
  (1 - sonicSpeed^2) * (3 + 2 * ell * sonicSpeed * sonicRadius beta * (1-beta))

def slopeC (beta : ℝ) : ℝ := (1 - sonicSpeed^2) * q beta

def resonancePolynomial (beta n : ℝ) : ℝ :=
  3 * n * (15 - 8 * beta)^2 - (n + 1)^2 * (5 * (9-2*beta)^2 - 243)

lemma sonicSpeed_sq : sonicSpeed^2 = 3/5 := by
  have he : (0 : ℝ) ≤ ell := by norm_num [ell]
  have hs := Real.sq_sqrt he
  have hn : Real.sqrt ell ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num [ell]))
  dsimp [sonicSpeed]
  field_simp
  nlinarith only [hs, show ell = (5:ℝ)/3 from rfl]

lemma sonicRadius_eq (beta : ℝ) : sonicRadius beta = 3*sonicSpeed/q beta := by
  simp only [sonicRadius, sonicSpeed, q, div_eq_mul_inv, mul_inv_rev]
  ring

lemma source_beta_lt_two {beta : ℝ}
    (hbeta : 1 < beta) (hupper : beta*(ell+Real.sqrt ell) < 3) : beta < 2 := by
  have hs : 0 ≤ Real.sqrt ell := Real.sqrt_nonneg _
  have hp : 0 < beta := by linarith
  have hmul := mul_nonneg (le_of_lt hp) hs
  dsimp [ell] at hupper
  dsimp [ell] at hmul
  nlinarith

lemma slope_coefficients {beta : ℝ} (hq : q beta ≠ 0) :
    slopeA beta = 6 * ((q beta)^2 - 27/5) / (q beta)^3 ∧
    slopeB beta = (2/5) * (15-8*beta) / q beta ∧
    slopeC beta = (2/5) * q beta := by
  have hc := sonicSpeed_sq
  rw [slopeA, slopeB, slopeC, sonicRadius_eq]
  dsimp [ell]
  constructor
  · field_simp
    nlinarith only [hc]
  constructor
  · field_simp
    rw [hc]
    dsimp [q, ell]
    ring
  · rw [hc]
    ring

lemma source_coefficients_positive {beta : ℝ}
    (hbeta : 1 < beta) (hupper : beta*(ell+Real.sqrt ell) < 3) :
    0 < slopeA beta ∧ 0 < slopeB beta ∧ 0 < slopeC beta := by
  obtain ⟨hc, hcp, hcu, hq, ha, ha1, _⟩ := source_parameter_bounds hbeta hupper
  have hq' : 0 < q beta := hq
  obtain ⟨_, hB, hC⟩ := slope_coefficients (ne_of_gt hq')
  have hbr : beta*ell < 3 := by
    have hmul := mul_pos (show 0 < beta by linarith) hcp
    have hrs : 0 < Real.sqrt ell := Real.sqrt_pos.mpr (by norm_num [ell])
    have hmul' := mul_pos (show 0 < beta by linarith) hrs
    nlinarith only [hupper, hmul']
  have hb15 : 0 < 15 - 8*beta := by dsimp [ell] at hbr; linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold slopeA
    have hrad : 0 < 1 - (sonicRadius beta)^2 := by nlinarith
    have he : (0 : ℝ) < ell := by norm_num [ell]
    positivity
  · rw [hB]
    exact div_pos (mul_pos (by norm_num) hb15) hq'
  · rw [hC]
    positivity

lemma source_slope_separation {beta : ℝ}
    (hbeta : 1 < beta) (hupper : beta*(ell+Real.sqrt ell) < 3) :
    (147/2) * (slopeA beta * slopeC beta) < (slopeB beta)^2 := by
  obtain ⟨_, _, _, hq, _⟩ := source_parameter_bounds hbeta hupper
  have hq' : 0 < q beta := hq
  obtain ⟨hA, hB, hC⟩ := slope_coefficients (ne_of_gt hq')
  have hb2 := source_beta_lt_two hbeta hupper
  have hp : 0 < (beta-1)*(11232-1278*beta) := by
    apply mul_pos <;> linarith
  rw [hA, hB, hC]
  apply (mul_lt_mul_iff_left₀ (sq_pos_of_pos hq')).mp
  field_simp
  dsimp [q, ell]
  nlinarith only [hp]

def sigma (beta : ℝ) : ℝ := 27 / (5 * (q beta)^2)
def kappa (beta : ℝ) : ℝ := 3 * (1-beta) / q beta

def normalizedDenom (beta z u : ℝ) : ℝ :=
  z * (1 - sigma beta*z^2) * (1-u^2)

def normalizedNumer (beta z u : ℝ) : ℝ :=
  (1-(3/5)*u^2) * (kappa beta*z*(1-u^2)+3*(z-u))

lemma normalized_denominator {beta : ℝ} (hq : q beta ≠ 0) (z u : ℝ) :
    sonicDenom ell (sonicRadius beta*z) (sonicSpeed*u) * (q beta/3) =
      sonicSpeed * normalizedDenom beta z u := by
  rw [sonicRadius_eq]
  unfold sonicDenom normalizedDenom sigma ell
  field_simp
  rw [sonicSpeed_sq]
  ring

lemma normalized_numerator {beta : ℝ} (hq : q beta ≠ 0) (z u : ℝ) :
    sonicNumer ell beta (sonicRadius beta*z) (sonicSpeed*u) =
      sonicSpeed * normalizedNumer beta z u := by
  rw [sonicRadius_eq]
  unfold sonicNumer normalizedNumer kappa ell
  field_simp
  rw [sonicSpeed_sq]
  dsimp [q, ell]
  ring

lemma normalized_equation_iff {beta : ℝ} (hq : q beta ≠ 0)
    (z u m : ℝ) :
    (sonicDenom ell (sonicRadius beta*z) (sonicSpeed*u) * (q beta/3*m) =
      sonicNumer ell beta (sonicRadius beta*z) (sonicSpeed*u)) ↔
       normalizedDenom beta z u*m = normalizedNumer beta z u := by
  rw [← mul_assoc, normalized_denominator hq, normalized_numerator hq, mul_assoc]
  have hc : sonicSpeed ≠ 0 := by
    have hs := sonicSpeed_sq
    intro h
    rw [h] at hs
    norm_num at hs
  exact mul_left_cancel₀ hc |> fun h => ⟨h, congrArg (sonicSpeed * ·)⟩

def jetA (beta : ℝ) : ℝ := 2*(1-sigma beta)
def jetB (beta : ℝ) : ℝ := (2/5)*(2*kappa beta+3)
def jetC : ℝ := 6/5

def jetLinear (beta s : ℝ) (n : ℕ) : ℝ :=
  jetB beta - jetA beta*s*(n+1)

lemma sigma_eq_radius_sq {beta : ℝ} (hq : q beta ≠ 0) :
    sigma beta = (sonicRadius beta)^2 := by
  rw [sonicRadius_eq]
  unfold sigma
  rw [div_pow, mul_pow, sonicSpeed_sq]
  field_simp
  ; ring

lemma jet_coefficients_positive {beta : ℝ}
    (hbeta : 1 < beta) (hupper : beta*(ell+Real.sqrt ell) < 3) :
    0 < jetA beta ∧ 0 < jetB beta ∧ 0 < jetC := by
  obtain ⟨_, _, _, hq, ha, ha1, _⟩ := source_parameter_bounds hbeta hupper
  have hq' : 0 < q beta := hq
  have hbet : beta*ell < 3 := by
    have hs : 0 < Real.sqrt ell := Real.sqrt_pos.mpr (by norm_num [ell])
    have hm := mul_pos (show 0 < beta by linarith) hs
    linarith
  have hB : jetB beta = (2/5)*(15-8*beta)/q beta := by
    unfold jetB kappa
    field_simp
    dsimp [q, ell]
    ring
  refine ⟨?_, ?_, by norm_num [jetC]⟩
  · rw [jetA, sigma_eq_radius_sq (ne_of_gt hq')]
    nlinarith
  · rw [hB]
    have hn : 0 < 15-8*beta := by dsimp [ell] at hbet; linarith
    positivity

lemma jet_resonance_identity {beta n : ℝ} (hq : q beta ≠ 0) :
    (75 * (q beta)^2) *
      (n * (jetB beta)^2 - (n+1)^2 * jetA beta * jetC) =
        4 * resonancePolynomial beta n := by
  unfold jetA jetB jetC sigma kappa resonancePolynomial
  field_simp
  dsimp [q, ell]
  ring

lemma exists_admissible_ratio73 : ∃ beta : ℝ,
    1 < beta ∧ beta*(ell+Real.sqrt ell) < 3 ∧
    resonancePolynomial beta 73 = 0 := by
  have hc : Continuous (fun beta => resonancePolynomial beta 73) := by
    unfold resonancePolynomial
    fun_prop
  have hm : (0 : ℝ) ∈ Set.Icc
      (resonancePolynomial 1 73) (resonancePolynomial (1001/1000) 73) := by
    norm_num [resonancePolynomial]
  obtain ⟨beta, hb, hz⟩ := intermediate_value_Icc
    (show (1:ℝ) ≤ 1001/1000 by norm_num) hc.continuousOn hm
  have hn : beta ≠ 1 := by
    intro h
    rw [h] at hz
    norm_num [resonancePolynomial] at hz
  have hbeta : 1 < beta := lt_of_le_of_ne hb.1 (Ne.symm hn)
  have hs : (Real.sqrt ell)^2 = ell := Real.sq_sqrt (by norm_num [ell])
  have hsr : Real.sqrt ell < 13/10 := by dsimp [ell] at hs ⊢; nlinarith
  have hmul := mul_lt_mul_of_pos_left hsr (show 0 < beta by linarith)
  refine ⟨beta, hbeta, ?_, hz⟩
  dsimp [ell] at hmul ⊢
  nlinarith [hb.2]

lemma exists_zero_jet_linear73 : ∃ beta s : ℝ,
    1 < beta ∧ beta*(ell+Real.sqrt ell) < 3 ∧ 0 < s ∧
    jetA beta*s^2 - jetB beta*s + jetC = 0 ∧
    jetLinear beta s 73 = 0 := by
  obtain ⟨beta, hbeta, hupper, hz⟩ := exists_admissible_ratio73
  obtain ⟨hA, hB, hC⟩ := jet_coefficients_positive hbeta hupper
  obtain ⟨_, _, _, hq, _⟩ := source_parameter_bounds hbeta hupper
  have hq' : 0 < q beta := hq
  have hi := jet_resonance_identity (n := 73) (ne_of_gt hq')
  rw [hz, mul_zero] at hi
  have hm : (75:ℝ)*(q beta)^2 ≠ 0 := by positivity
  have hr := (mul_eq_zero.mp hi).resolve_left hm
  let s := jetB beta / (74*jetA beta)
  have hs : 0 < s := div_pos hB (mul_pos (by norm_num) hA)
  refine ⟨beta, s, hbeta, hupper, hs, ?_, ?_⟩
  · dsimp [s]
    field_simp
    linear_combination -hr
  · dsimp [jetLinear, s]
    norm_num
    field_simp
    ; ring

end SepticProfile

end
end

end OAI
