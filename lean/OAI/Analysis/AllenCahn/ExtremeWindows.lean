import OAI.Analysis.AllenCahn.EllipticCompactness
import OAI.Analysis.AllenCahn.ExtremeRays

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open MeasureTheory intervalIntegral Set Filter Topology

lemma sech_neg (y : ℝ) : sech (-y) = sech y := by simp [sech]

lemma exp_two_sech_four (y : ℝ) :
    Real.exp (2*y)*sech y^4 = (1+Real.tanh y)^2*sech y^2 := by
  rw [show 2*y = y+y by ring, Real.exp_add, ←Real.cosh_add_sinh y,
    Real.tanh_eq_sinh_div_cosh y]
  dsimp [sech]
  field_simp

lemma exp_two_sech_four_primitive (y : ℝ) :
    HasDerivAt (fun z => Real.tanh z + Real.tanh z^2 + Real.tanh z^3/3)
      (Real.exp (2*y)*sech y^4) y := by
  convert ((tanh_hasDerivAt y).add ((tanh_hasDerivAt y).pow 2)).add
    (((tanh_hasDerivAt y).pow 3).div_const 3) using 1
  first | rfl | (rw [exp_two_sech_four]; ring)

lemma integral_exp_two_sech_four (R : ℝ) :
    (∫ y in -R..R, Real.exp (2*y)*sech y^4) =
      2*Real.tanh R + (2/3)*Real.tanh R^3 := by
  have hi : IntervalIntegrable (fun y => Real.exp (2*y)*sech y^4) volume (-R) R :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (contDiff_sech.continuous.pow 4)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => exp_two_sech_four_primitive y) hi]
  rw [Real.tanh_neg]
  ring

lemma moment_exp_two_sech_four (R : ℝ) :
    (∫ y in -R..R, y*Real.exp (2*y)*sech y^4) =
      2*Real.tanh R - 2*R*sech R^2 := by
  let k := fun y : ℝ => y*Real.exp (2*y)*sech y^4
  have hk : Continuous k := (continuous_id.mul (Real.continuous_exp.comp
    (continuous_const.mul continuous_id))).mul (contDiff_sech.continuous.pow 4)
  have href : (∫ y in -R..R, k (-y)) = ∫ y in -R..R, k y := by
    simpa only [neg_neg] using (intervalIntegral.integral_comp_neg (f := k) (a := -R) (b := R))
  have hki : IntervalIntegrable k volume (-R) R := hk.intervalIntegrable _ _
  have hkni : IntervalIntegrable (fun y => k (-y)) volume (-R) R := (hk.comp continuous_neg).intervalIntegrable _ _
  have hsum : (∫ y in -R..R, k y + k (-y)) = 2*(∫ y in -R..R, k y) := by
    rw [intervalIntegral.integral_add hki hkni, href]
    ring
  have he (y) : k y + k (-y) = 4*y*Real.tanh y*sech y^2 := by
    dsimp [k]
    rw [mul_assoc y, exp_two_sech_four, mul_assoc (-y), exp_two_sech_four,
      Real.tanh_neg, sech_neg]
    ring
  have hd (y) : HasDerivAt (fun z => 2*(Real.tanh z-z*sech z^2))
      (4*y*Real.tanh y*sech y^2) y := by
    convert ((tanh_hasDerivAt y).sub ((hasDerivAt_id y).mul
      ((sech_hasDerivAt' y).pow 2))).const_mul 2 using 1 <;> first | rfl | (try simp only [Pi.pow_apply, id_eq]; ring)
  have hcalc : (∫ y in -R..R, 4*y*Real.tanh y*sech y^2) =
      4*Real.tanh R-4*R*sech R^2 := by
    have hi : IntervalIntegrable (fun y => 4*y*Real.tanh y*sech y^2) volume (-R) R :=
      (((continuous_const.mul continuous_id).mul contDiff_tanh.continuous).mul
        (contDiff_sech.continuous.pow 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) hi]
    rw [Real.tanh_neg, sech_neg]
    ring
  have : (∫ y in -R..R, k y+k (-y)) = ∫ y in -R..R, 4*y*Real.tanh y*sech y^2 := by
    apply intervalIntegral.integral_congr
    intro y _; exact he y
  rw [hsum, hcalc] at this
  dsimp [k] at this
  linarith

lemma exp_tangent_two (a y : ℝ) :
    Real.exp (2*y)*(1+(a-2)*y) ≤ Real.exp (a*y) := by
  have H := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((a-2)*y)) (Real.exp_pos (2*y)).le
  rw [←Real.exp_add] at H
  convert H using 1 <;> congr 1 <;> ring

lemma finite_mass_tangent {R a : ℝ} (hR : 0 ≤ R) (ha : a ≤ 2) :
    (3/4)*(∫ y in -R..R, Real.exp (a*y)*sech y^4) ≥
      (3/2)*a-3+(3/4)*(2*Real.tanh R+(2/3)*Real.tanh R^3) := by
  have hk0 : Continuous (fun y : ℝ => Real.exp (2*y)*sech y^4) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (contDiff_sech.continuous.pow 4)
  have hk1 : Continuous (fun y : ℝ => y*Real.exp (2*y)*sech y^4) :=
    (continuous_id.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul (contDiff_sech.continuous.pow 4)
  have hka : Continuous (fun y : ℝ => Real.exp (a*y)*sech y^4) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (contDiff_sech.continuous.pow 4)
  have hi0 : IntervalIntegrable (fun y => Real.exp (2*y)*sech y^4) volume (-R) R := hk0.intervalIntegrable _ _
  have hi1 : IntervalIntegrable (fun y => (a-2)*(y*Real.exp (2*y)*sech y^4)) volume (-R) R := (continuous_const.mul hk1).intervalIntegrable _ _
  have hia : IntervalIntegrable (fun y => Real.exp (a*y)*sech y^4) volume (-R) R := hka.intervalIntegrable _ _
  have H : (∫ y in -R..R, Real.exp (2*y)*sech y^4 +
      (a-2)*(y*Real.exp (2*y)*sech y^4)) ≤ ∫ y in -R..R, Real.exp (a*y)*sech y^4 := by
    apply intervalIntegral.integral_mono_on (by linarith : -R ≤ R)
      (hi0.add hi1) hia
    intro y _
    have HH := mul_le_mul_of_nonneg_right (exp_tangent_two a y) (by positivity : 0 ≤ sech y^4)
    calc Real.exp (2*y)*sech y^4+(a-2)*(y*Real.exp (2*y)*sech y^4) =
        Real.exp (2*y)*(1+(a-2)*y)*sech y^4 := by ring
      _ ≤ Real.exp (a*y)*sech y^4 := HH
  rw [intervalIntegral.integral_add hi0 hi1,
    intervalIntegral.integral_const_mul, integral_exp_two_sech_four, moment_exp_two_sech_four] at H
  have hm : 2*Real.tanh R - 2*R*sech R^2 ≤ 2 := by
    nlinarith [Real.tanh_lt_one R, mul_nonneg hR (sq_nonneg (sech R))]
  nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ha) (sub_nonneg.mpr hm)]

lemma jost_weighted_primitive (a y : ℝ) :
    HasDerivAt (fun z => Real.exp (a*z)*sech z^4)
      (4*(jost a y*sech y^4) - 3*a*(Real.exp (a*y)*sech y^4)) y := by
  convert (((hasDerivAt_id y).const_mul a).exp.mul ((sech_hasDerivAt' y).pow 4)) using 1 <;> first | rfl | (dsimp [jost]; ring)

lemma finite_jost_mass_lower {R a : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a) :
    (3*a/4)*(∫ y in -R..R, Real.exp (a*y)*sech y^4) ≤
      ∫ y in -R..R, jost a y*sech y^4 := by
  have hk : Continuous (fun y : ℝ => Real.exp (a*y)*sech y^4) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (contDiff_sech.continuous.pow 4)
  have hj : Continuous (fun y : ℝ => jost a y*sech y^4) :=
    (contDiff_jost a).continuous.mul (contDiff_sech.continuous.pow 4)
  have hij : IntervalIntegrable (fun y => 4*(jost a y*sech y^4)) volume (-R) R := (continuous_const.mul hj).intervalIntegrable _ _
  have hik : IntervalIntegrable (fun y => 3*a*(Real.exp (a*y)*sech y^4)) volume (-R) R := (continuous_const.mul hk).intervalIntegrable _ _
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -R) (b := R) (fun y _ => jost_weighted_primitive a y) (hij.sub hik)
  rw [intervalIntegral.integral_sub hij hik,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, sech_neg] at H
  have hh : Real.exp (a*(-R)) ≤ Real.exp (a*R) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ sech R^4)]

lemma reflected_weighted_mass (R a : ℝ) :
    (∫ y in -R..R, jostReflected a y*sech y^4) =
      ∫ y in -R..R, jost a y*sech y^4 := by
  have H := intervalIntegral.integral_comp_neg
    (f := fun y => jost a y*sech y^4) (a := -R) (b := R)
  simpa only [jost_reflection, sech_neg, neg_neg] using H

lemma tanh_exp_two (y : ℝ) :
    Real.tanh y = (Real.exp (2*y)-1)/(Real.exp (2*y)+1) := by
  have he : Real.exp (2*y) = Real.exp y ^ 2 := by
    rw [show 2*y=y+y by ring, Real.exp_add, pow_two]
  rw [Real.tanh_eq, he, Real.exp_neg]
  apply (div_eq_div_iff (by positivity : Real.exp y+(Real.exp y)⁻¹ ≠ 0)
    (by positivity : Real.exp y^2+1 ≠ 0)).mpr
  field_simp

lemma tanh_nonneg_of_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ Real.tanh R := by
  rw [tanh_exp_two]
  apply div_nonneg
  · linarith [Real.add_one_le_exp (2*R)]
  · positivity

lemma tanh_tail_bound {R : ℝ} (hR : 0 < R) : 1-Real.tanh R ≤ 1/R := by
  have hh : 1-Real.tanh R = 2/(Real.exp (2*R)+1) := by
    rw [tanh_exp_two]
    field_simp
    ring
  rw [hh]
  apply (div_le_div_iff₀ (by positivity) hR).mpr
  linarith [Real.add_one_le_exp (2*R)]

lemma exp_two_mass_deficit {R : ℝ} (hR : 0 < R) :
    2-(3/4)*(2*Real.tanh R+(2/3)*Real.tanh R^3) ≤ 3/R := by
  have ht0 := tanh_nonneg_of_nonneg hR.le
  have htt := Real.tanh_lt_one R
  have hE : 2-(3/4)*(2*Real.tanh R+(2/3)*Real.tanh R^3) ≤ 3*(1-Real.tanh R) := by
    nlinarith [mul_nonneg (sq_nonneg (1-Real.tanh R)) (by linarith : 0 ≤ Real.tanh R+2)]
  have H := mul_le_mul_of_nonneg_left (tanh_tail_bound hR) (by norm_num : (0 : ℝ) ≤ 3)
  have he : 3 * (1 / R) = 3 / R := by ring
  rw [he] at H
  exact hE.trans H

lemma jost_finite_window {c : ℝ} (hc : 3/4 < c) :
    ∃ R > (0 : ℝ), ∀ a ∈ Icc (1 : ℝ) 2,
      a^2-1 ≤ c*(∫ y in -R..R, jost a y*sech y^4) := by
  have hc0 : 0 < c := by linarith
  let δ := 1-(3/4)/c
  have hδ : 0 < δ := by dsimp [δ]; exact sub_pos.mpr ((div_lt_one hc0).mpr hc)
  have hδ1 : δ < 1 := by dsimp [δ]; have := div_pos (by norm_num : (0:ℝ)<3/4) hc0; linarith
  have hcd : c*(1-δ) = 3/4 := by dsimp [δ]; field_simp; ring
  let R := 6/δ
  have hR : 0 < R := div_pos (by norm_num) hδ
  have hERR : 2-(3/4)*(2*Real.tanh R+(2/3)*Real.tanh R^3) ≤ δ/2 := by
    have H := exp_two_mass_deficit hR
    have hh : 3/R = δ/2 := by dsimp [R]; field_simp; ring
    rwa [hh] at H
  refine ⟨R, hR, ?_⟩
  intro a ha
  have ha0 : 0 ≤ a := by linarith [ha.1]
  let M := (3/4)*(∫ y in -R..R, Real.exp (a*y)*sech y^4)
  have hM : (1-δ)*((3/2)*a-1) ≤ M := by
    have H := finite_mass_tangent hR.le ha.2
    dsimp [M]
    nlinarith [mul_nonneg hδ.le (by linarith [ha.1] : 0 ≤ (3/2)*a-3/2)]
  have hJ : (1-δ)*(a*((3/2)*a-1)) ≤ ∫ y in -R..R, jost a y*sech y^4 := by
    have H := mul_le_mul_of_nonneg_left hM ha0
    have HH := finite_jost_mass_lower hR.le ha0
    dsimp [M] at H
    nlinarith
  have hpoly : (4/3)*(a^2-1) ≤ a*((3/2)*a-1) := by
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (by linarith [ha.2] : a-2 ≤ 0)
      (by linarith [ha.2] : a-4 ≤ 0)]
  calc a^2-1 = c*((1-δ)*((4/3)*(a^2-1))) := by rw [←mul_assoc, hcd]; ring
       _ ≤ c*((1-δ)*(a*((3/2)*a-1))) :=
         mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpoly (by linarith)) hc0.le
       _ ≤ c*(∫ y in -R..R, jost a y*sech y^4) := mul_le_mul_of_nonneg_left hJ hc0.le

lemma positive_sech_ode_finite_window {c : ℝ} (hc : 3/4 < c) :
    ∃ R > (0 : ℝ), ∀ (f : ℝ → ℝ) (lam : ℝ), ContDiff ℝ 2 f →
      (∀ y, 0 < f y) → lam ≤ 4 →
      (∀ y, deriv (deriv f) y = (lam-2*sech y^2)*f y) →
      |deriv f 0| ≤ c*(∫ y in -R..R, f y*sech y^4) := by
  obtain ⟨R, hR, hbound⟩ := jost_finite_window hc
  have hc0 : 0 ≤ c := by linarith
  refine ⟨R, hR, ?_⟩
  intro f lam hf hp hlam hode
  have hl := positive_sech_ode_spectral hf hp hode
  let a := Real.sqrt lam
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hasq : a^2 = lam := Real.sq_sqrt (by linarith)
  have ha1 : 1 ≤ a := by nlinarith
  have ha2 : a ≤ 2 := by nlinarith
  have hmass : 0 ≤ ∫ y in -R..R, f y*sech y^4 := by
    apply intervalIntegral.integral_nonneg (by linarith : -R ≤ R)
    intro y _; exact mul_nonneg (hp y).le (pow_nonneg (le_of_lt (sech_pos y)) 4)
  rcases eq_or_lt_of_le ha1 with he | he
  · have hla : lam = 1 := by rw [←hasq, ←he]; norm_num
    have hrepr := positive_sech_ode_endpoint hf hp (by simpa only [hla] using hode)
    have hfeq : f = fun y => f 0*sech y := funext hrepr
    have hd : deriv f 0 = 0 := by
      have HH := (sech_hasDerivAt 0).const_mul (f 0)
      have HH' : HasDerivAt f 0 0 := by
        simpa only [←hfeq, Real.sinh_zero, zero_div, mul_zero, neg_zero] using HH
      exact HH'.deriv
    rw [hd, abs_zero]
    exact mul_nonneg hc0 hmass
  · obtain ⟨A, B, hA, hB, hAB, hrepr⟩ := positive_sech_ode_classification he hf hp
      (fun y => by rw [hasq]; exact hode y)
    have hfeq : f = fun y => A*jost a y+B*jostReflected a y := funext hrepr
    have hd : deriv f 0 = (A-B)*(a^2-1) := by
      have HH := ((jost_hasDerivAt a 0).const_mul A).add
        (((contDiff_jostReflected a).differentiable (by simp) 0).hasDerivAt.const_mul B)
      have HH' : HasDerivAt (fun y => A*jost a y+B*jostReflected a y)
          ((A-B)*(a^2-1)) 0 := by
        have hv : A*(Real.exp (a*0)*(a*(a-Real.tanh 0)-sech 0^2)) +
            B*deriv (jostReflected a) 0 = (A-B)*(a^2-1) := by
          rw [jostReflected_deriv_at_zero]
          simp only [mul_zero, Real.exp_zero, Real.tanh_zero, sech, Real.cosh_zero, inv_one]
          ring
        rw [hv] at HH
        exact HH
      rw [hfeq]
      exact HH'.deriv
    have hjI : IntervalIntegrable (fun y => A*(jost a y*sech y^4)) volume (-R) R :=
      (continuous_const.mul ((contDiff_jost a).continuous.mul (contDiff_sech.continuous.pow 4))).intervalIntegrable _ _
    have hkI : IntervalIntegrable (fun y => B*(jostReflected a y*sech y^4)) volume (-R) R :=
      (continuous_const.mul ((contDiff_jostReflected a).continuous.mul (contDiff_sech.continuous.pow 4))).intervalIntegrable _ _
    have hmassEq : (∫ y in -R..R, f y*sech y^4) =
        (A+B)*(∫ y in -R..R, jost a y*sech y^4) := by
      have heq : (fun y => f y*sech y^4) = fun y =>
          A*(jost a y*sech y^4)+B*(jostReflected a y*sech y^4) := by
        funext y; rw [hrepr]; ring
      rw [heq, intervalIntegral.integral_add hjI hkI,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, reflected_weighted_mass]
      ring
    have hsq : 0 ≤ a^2-1 := by nlinarith
    have habs : |A-B| ≤ A+B := by
      rw [abs_le]; constructor <;> linarith
    rw [hd, abs_mul, abs_of_nonneg hsq, hmassEq]
    calc |A-B| * (a^2-1) ≤ (A+B)*(a^2-1) := mul_le_mul_of_nonneg_right habs hsq
         _ ≤ (A+B)*(c*(∫ y in -R..R, jost a y*sech y^4)) :=
           mul_le_mul_of_nonneg_left (hbound a ⟨ha1, ha2⟩) (add_nonneg hA hB)
         _ = c*((A+B)*(∫ y in -R..R, jost a y*sech y^4)) := by ring

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open DeGiorgiCompactness (JetSpace CoherentJets pdeJetCone jetDirectional jetSegmentMass)

lemma jetCone_extreme_base {n : ℕ} {P : Space n → ℝ} {g : JetSpace n}
    (hg : g ∈ (pdeJetCone P).extremePoints ℝ) :
    (g [] : Space n → ℝ) ∈ (positiveLinearCone P).extremePoints ℝ := by
  refine ⟨jetCone_base_mem hg.1, ?_⟩
  intro f hf h hh hseg
  rcases hseg with ⟨a,b,ha,hb,hab,he⟩
  let F := smoothJet f hf.1
  let H := smoothJet h hh.1
  have hF : F ∈ pdeJetCone P := smoothJet_mem hf
  have hH : H ∈ pdeJetCone P := smoothJet_mem hh
  have heq : a • F+b • H = g := by
    apply DeGiorgiCompactness.coherentJets_eq_of_base
      (DeGiorgiCompactness.coherentJets_add_smul hF.1 hH.1 a b) hg.1.1
    ext x
    exact congrFun he x
  have hhseg : g ∈ openSegment ℝ F H := ⟨a,b,ha,hb,hab,heq⟩
  have hFG := hg.2 hF hH hhseg
  funext x
  exact congrArg (fun q : JetSpace n => q [] x) hFG

lemma jetDirectional_eq_fderiv {n : ℕ} {g : JetSpace n} (hg : CoherentJets g)
    (ξ : Space n) : jetDirectional ξ g = fderiv ℝ (g [] : Space n → ℝ) 0 ξ := by
  unfold jetDirectional
  have he : (fun i => g [i] 0) = fun i => DeGiorgiCompactness.coordDeriv (g []) i 0 :=
    funext (fun i => ((hg []).2 i 0).symm)
  rw [he, DeGiorgiCompactness.coordinateDual_fderiv]

lemma deriv_normal_line {n : ℕ} {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (ξ : Space n) : deriv (fun t : ℝ => f (t • ξ)) 0 = fderiv ℝ f 0 ξ := by
  have hd : HasDerivAt (fun t : ℝ => t • ξ) ξ 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const ξ)
  have H := ((hf (0 • ξ)).hasFDerivAt).comp_hasDerivAt 0 hd
  simpa only [id_eq, one_smul, zero_smul, Function.comp_def] using H.deriv

lemma conePotential_extreme_window {c : ℝ} (hc : 3/4 < c) :
    ∃ R > (0 : ℝ), ∀ {n : ℕ} {ν : Space n}, ‖ν‖=1 →
      ∀ g ∈ (pdeJetCone (conePotential ν)).extremePoints ℝ,
      |jetDirectional (Real.sqrt 2 • ν) g| ≤
        c*jetSegmentMass (Real.sqrt 2 • ν) (fun y => sech y^4) R g := by
  obtain ⟨R,hR,hbound⟩ := positive_sech_ode_finite_window hc
  refine ⟨R,hR, ?_⟩
  intro n ν hν g hg
  have hf := jetCone_extreme_base hg
  obtain ⟨b,F,hb,hFs,hFp,hF0,hrep,hode⟩ := conePotential_extreme_separated hν hf
  have hνν : inner ℝ ν ν = 1 := by rw [real_inner_self_eq_norm_sq, hν]; norm_num
  have he : F = fun y : ℝ => g [] (y • (Real.sqrt 2 • ν)) := by
    funext y
    have H := hrep (y • (Real.sqrt 2 • ν))
    rw [real_inner_smul_right, real_inner_smul_right, hb, mul_zero, mul_zero,
      Real.exp_zero, one_mul, real_inner_smul_right, real_inner_smul_right, hνν,
      mul_one] at H
    have harg : y*Real.sqrt 2/Real.sqrt 2 = y := by field_simp
    rw [harg] at H
    exact H.symm
  have HH := hbound F (4-2*‖b‖^2) (hFs.of_le (WithTop.coe_le_coe.mpr le_top)) hFp (by nlinarith [sq_nonneg ‖b‖]) hode
  rw [he, deriv_normal_line ((jetCone_base_mem hg.1).1.differentiable (by simp))] at HH
  rw [jetDirectional_eq_fderiv hg.1.1]
  exact HH

end DeGiorgi
end

end OAI
