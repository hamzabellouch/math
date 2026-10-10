import OAI.Analysis.AllenCahn.PositiveCone

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff

lemma positive_sech_ode_spectral {f : ℝ → ℝ} {lam : ℝ}
    (hf : ContDiff ℝ 2 f) (hp : ∀ y, 0 < f y)
    (heq : ∀ y, deriv (deriv f) y = (lam - 2 * sech y ^ 2) * f y) : 1 ≤ lam := by
  by_contra hlam
  have hlam : lam < 1 := lt_of_not_ge hlam
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfdd : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  let W := fun y => deriv f y * sech y - f y * deriv sech y
  let w := fun y => f y * Real.cosh y
  have hsd : Differentiable ℝ sech := contDiff_sech.differentiable (by simp)
  have hWd (y) : HasDerivAt W ((lam-1)*f y*sech y) y := by
    have H := ((hfdd y).hasDerivAt.mul (sech_hasDerivAt y)).sub
      ((hfd y).hasDerivAt.mul (sech_hasDerivAt_twice y))
    change HasDerivAt W (deriv (deriv f) y * sech y + deriv f y *
      (-Real.sinh y / Real.cosh y ^ 2) -
      (deriv f y * deriv sech y + f y * ((1 - 2 * sech y ^ 2) * sech y))) y at H
    rw [heq y, ← sech_deriv y] at H
    have he : (lam - 2 * sech y ^ 2) * f y * sech y + deriv f y * deriv sech y -
      (deriv f y * deriv sech y + f y * ((1 - 2 * sech y ^ 2) * sech y)) =
      (lam-1)*f y*sech y := by ring
    rwa [he] at H
  have hW : Antitone W := antitone_of_deriv_nonpos
    (fun y => (hWd y).differentiableAt) (fun y => by
      rw [(hWd y).deriv]; exact le_of_lt (mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by linarith) (hp y)) (sech_pos y)))
  have hwd (y) : HasDerivAt w (W y * Real.cosh y ^ 2) y := by
    have H := (hfd y).hasDerivAt.mul (Real.hasDerivAt_cosh y)
    change HasDerivAt w (deriv f y * Real.cosh y + f y * Real.sinh y) y at H
    have he : deriv f y * Real.cosh y + f y * Real.sinh y = W y * Real.cosh y ^ 2 := by
      dsimp [W]
      rw [sech_deriv]
      dsimp [sech]
      field_simp
      ring
    rwa [he] at H
  have hzero := positive_antitone_flux_zero (fun y => (hwd y).differentiableAt)
    (fun y => mul_pos (hp y) (Real.cosh_pos y)) hW cosh_sq_ge_one
    (fun y => (hwd y).deriv)
  have hconst : W = fun _ => 0 := funext hzero
  have hs : (lam-1)*f 0*sech 0 = 0 := by
    have H := (hWd 0).deriv
    rw [hconst, deriv_const] at H
    exact H.symm
  have hn : (lam-1)*f 0*sech 0 < 0 := mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (by linarith) (hp 0)) (sech_pos 0)
  linarith

lemma positive_sech_ode_endpoint {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hp : ∀ y, 0 < f y)
    (heq : ∀ y, deriv (deriv f) y = (1 - 2 * sech y ^ 2) * f y) :
    ∀ y, f y = f 0 * sech y := by
  have hfd := hf.differentiable (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have hfdd := hf.differentiable_deriv_two
  let W := fun y => deriv f y * sech y - f y * deriv sech y
  let w := fun y => f y * Real.cosh y
  have hWd (y) : HasDerivAt W 0 y := by
    have H := ((hfdd y).hasDerivAt.mul (sech_hasDerivAt y)).sub
      ((hfd y).hasDerivAt.mul (sech_hasDerivAt_twice y))
    change HasDerivAt W (deriv (deriv f) y * sech y + deriv f y *
      (-Real.sinh y / Real.cosh y ^ 2) -
      (deriv f y * deriv sech y + f y * ((1 - 2 * sech y ^ 2) * sech y))) y at H
    rw [heq y, ← sech_deriv y] at H
    have he : (1 - 2 * sech y ^ 2) * f y * sech y + deriv f y * deriv sech y -
      (deriv f y * deriv sech y + f y * ((1 - 2 * sech y ^ 2) * sech y)) = 0 := by ring
    rwa [he] at H
  have hW : Antitone W := antitone_of_deriv_nonpos
    (fun y => (hWd y).differentiableAt) (fun y => by rw [(hWd y).deriv])
  have hwd (y) : HasDerivAt w (W y * Real.cosh y ^ 2) y := by
    have H := (hfd y).hasDerivAt.mul (Real.hasDerivAt_cosh y)
    change HasDerivAt w (deriv f y * Real.cosh y + f y * Real.sinh y) y at H
    have he : deriv f y * Real.cosh y + f y * Real.sinh y = W y * Real.cosh y ^ 2 := by
      dsimp [W]
      rw [sech_deriv]
      dsimp [sech]
      field_simp
      ring
    rwa [he] at H
  have hzero := positive_antitone_flux_zero (fun y => (hwd y).differentiableAt)
    (fun y => mul_pos (hp y) (Real.cosh_pos y)) hW cosh_sq_ge_one
    (fun y => (hwd y).deriv)
  intro y
  have H := is_const_of_deriv_eq_zero (fun y => (hwd y).differentiableAt)
    (fun y => by rw [(hwd y).deriv, hzero y, zero_mul]) y 0
  dsimp [w] at H
  simp only [Real.cosh_zero, mul_one] at H
  dsimp [sech]
  rw [← H]
  field_simp

lemma wronskian_eq_initial {V f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfe : ∀ y, deriv (deriv f) y = V y * f y)
    (hge : ∀ y, deriv (deriv g) y = V y * g y) (y : ℝ) :
    deriv f y * g y - f y * deriv g y = deriv f 0 * g 0 - f 0 * deriv g 0 := by
  let W := fun y => deriv f y * g y - f y * deriv g y
  have hd (y) : HasDerivAt W 0 y := by
    have H := ((hf.differentiable_deriv_two y).hasDerivAt.mul
      ((hg.differentiable (by norm_num)) y).hasDerivAt).sub
      (((hf.differentiable (by norm_num)) y).hasDerivAt.mul
        (hg.differentiable_deriv_two y).hasDerivAt)
    change HasDerivAt W (deriv (deriv f) y * g y + deriv f y * deriv g y -
      (deriv f y * deriv g y + f y * deriv (deriv g) y)) y at H
    rw [hfe y, hge y] at H
    have he : V y * f y * g y + deriv f y * deriv g y -
      (deriv f y * deriv g y + f y * (V y * g y)) = 0 := by ring
    rwa [he] at H
  exact is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
    (fun y => (hd y).deriv) y 0

lemma ode_basis_expansion {V f g h : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h)
    (hfe : ∀ y, deriv (deriv f) y = V y * f y)
    (hge : ∀ y, deriv (deriv g) y = V y * g y)
    (hhe : ∀ y, deriv (deriv h) y = V y * h y)
    (hdet : deriv g 0 * h 0 - g 0 * deriv h 0 ≠ 0) :
    ∀ y, f y = ((deriv f 0 * h 0 - f 0 * deriv h 0) /
        (deriv g 0 * h 0 - g 0 * deriv h 0)) * g y +
      ((deriv g 0 * f 0 - g 0 * deriv f 0) /
        (deriv g 0 * h 0 - g 0 * deriv h 0)) * h y := by
  intro y
  have Hfg := wronskian_eq_initial hf hh hfe hhe y
  have Hgh := wronskian_eq_initial hg hh hge hhe y
  have Hgf := wronskian_eq_initial hg hf hge hfe y
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  apply (eq_div_iff hdet).mpr
  nlinarith [congrArg (fun t => t * f y) Hgh,
    congrArg (fun t => t * g y) Hfg, congrArg (fun t => t * h y) Hgf]

lemma contDiff_tanh : ContDiff ℝ ∞ Real.tanh := by
  have H : Real.tanh = fun y => Real.sinh y / Real.cosh y := funext Real.tanh_eq_sinh_div_cosh
  rw [H]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun y => (Real.cosh_pos y).ne')

lemma tanh_hasDerivAt (y : ℝ) : HasDerivAt Real.tanh (sech y ^ 2) y := by
  have H := (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (Real.cosh_pos y).ne'
  change HasDerivAt (fun z => Real.sinh z / Real.cosh z)
    ((Real.cosh y * Real.cosh y - Real.sinh y * Real.sinh y) / Real.cosh y ^ 2) y at H
  have he : (Real.cosh y * Real.cosh y - Real.sinh y * Real.sinh y) / Real.cosh y ^ 2 = sech y ^ 2 := by
    rw [← pow_two, ← pow_two, Real.cosh_sq_sub_sinh_sq]
    simp [sech, one_div]
  rw [he, ← funext Real.tanh_eq_sinh_div_cosh] at H
  exact H

lemma sech_sq_tanh (y : ℝ) : sech y ^ 2 + Real.tanh y ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  dsimp [sech]
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq y]

def jost (a y : ℝ) : ℝ := Real.exp (a*y) * (a-Real.tanh y)

lemma contDiff_jost (a : ℝ) : ContDiff ℝ ∞ (jost a) :=
  (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul (contDiff_const.sub contDiff_tanh)

lemma jost_hasDerivAt (a y : ℝ) :
    HasDerivAt (jost a) (Real.exp (a*y) * (a*(a-Real.tanh y)-sech y^2)) y := by
  have H := ((hasDerivAt_id y).const_mul a).exp.mul ((hasDerivAt_const y a).sub (tanh_hasDerivAt y))
  change HasDerivAt (jost a)
    (Real.exp (a * y) * (a * 1) * (a - Real.tanh y) + Real.exp (a*y) * (0-sech y^2)) y at H
  convert H using 1
  ring

lemma jost_deriv (a y : ℝ) : deriv (jost a) y =
    Real.exp (a*y) * (a*(a-Real.tanh y)-sech y^2) := (jost_hasDerivAt a y).deriv

lemma sech_hasDerivAt' (y : ℝ) : HasDerivAt sech (-sech y * Real.tanh y) y := by
  have H := sech_hasDerivAt y
  have he : -Real.sinh y / Real.cosh y ^ 2 = -sech y * Real.tanh y := by
    rw [Real.tanh_eq_sinh_div_cosh]
    dsimp [sech]
    field_simp
  rwa [he] at H

lemma jost_hasDerivAt_twice (a y : ℝ) :
    HasDerivAt (deriv (jost a)) ((a^2-2*sech y^2)*jost a y) y := by
  have H := ((hasDerivAt_id y).const_mul a).exp.mul
    ((((hasDerivAt_const y a).sub (tanh_hasDerivAt y)).const_mul a).sub ((sech_hasDerivAt' y).pow 2))
  change HasDerivAt (fun z => Real.exp (a*z)*(a*(a-Real.tanh z)-sech z^2))
    (Real.exp (a*y)*(a*1)*(a*(a-Real.tanh y)-sech y^2) +
      Real.exp (a*y)*(a*(0-sech y^2) - 2*sech y^(2-1)*(-sech y*Real.tanh y))) y at H
  have he : Real.exp (a*y)*(a*1)*(a*(a-Real.tanh y)-sech y^2) +
      Real.exp (a*y)*(a*(0-sech y^2) - 2*sech y^(2-1)*(-sech y*Real.tanh y)) =
      (a^2-2*sech y^2)*jost a y := by dsimp [jost]; ring
  rw [he, ← funext (jost_deriv a)] at H
  exact H

def jostReflected (a y : ℝ) : ℝ := Real.exp (-a*y) * (a+Real.tanh y)

lemma jost_neg_parameter (a y : ℝ) : -jost (-a) y = jostReflected a y := by
  dsimp [jost, jostReflected]; ring

lemma jost_reflection (a y : ℝ) : jost a (-y) = jostReflected a y := by
  simp only [jost, jostReflected, Real.tanh_neg]
  congr 1 <;> congr 1 <;> ring

lemma contDiff_jostReflected (a : ℝ) : ContDiff ℝ ∞ (jostReflected a) := by
  rw [← funext (jost_neg_parameter a)]
  exact (contDiff_jost (-a)).neg

lemma jostReflected_deriv (a y : ℝ) : deriv (jostReflected a) y = -deriv (jost (-a)) y := by
  rw [← funext (jost_neg_parameter a)]
  exact deriv.fun_neg

lemma jost_ode (a y : ℝ) : deriv (deriv (jost a)) y = (a^2-2*sech y^2)*jost a y :=
  (jost_hasDerivAt_twice a y).deriv

lemma jostReflected_ode (a y : ℝ) : deriv (deriv (jostReflected a)) y =
    (a^2-2*sech y^2)*jostReflected a y := by
  rw [funext (jostReflected_deriv a), deriv.fun_neg, jost_ode]
  rw [← jost_neg_parameter]
  ring

lemma jost_pos {a : ℝ} (ha : 1 < a) (y : ℝ) : 0 < jost a y :=
  mul_pos (Real.exp_pos _) (by linarith [Real.tanh_lt_one y])

lemma jostReflected_pos {a : ℝ} (ha : 1 < a) (y : ℝ) : 0 < jostReflected a y :=
  mul_pos (Real.exp_pos _) (by linarith [Real.neg_one_lt_tanh y])

lemma jost_at_zero (a : ℝ) : jost a 0 = a := by simp [jost]

lemma jostReflected_at_zero (a : ℝ) : jostReflected a 0 = a := by simp [jostReflected]

lemma jost_deriv_at_zero (a : ℝ) : deriv (jost a) 0 = a^2-1 := by
  rw [jost_deriv]; simp [sech]; ring

lemma jostReflected_deriv_at_zero (a : ℝ) : deriv (jostReflected a) 0 = -(a^2-1) := by
  rw [jostReflected_deriv, jost_deriv_at_zero]; ring

lemma jost_scale (a y : ℝ) : jost a y * Real.exp (-a*y) = a-Real.tanh y := by
  dsimp [jost]
  rw [mul_right_comm, ← Real.exp_add]
  have he : a*y+-a*y=0 := by ring
  rw [he, Real.exp_zero, one_mul]

lemma jostReflected_scale (a y : ℝ) : jostReflected a y * Real.exp (-a*y) =
    Real.exp ((-2*a)*y) * (a+Real.tanh y) := by
  dsimp [jostReflected]
  rw [mul_right_comm, ← Real.exp_add]
  congr 2
  ring

lemma positive_jost_combination_first_nonneg {a A B : ℝ} (ha : 1 < a)
    (hp : ∀ y, 0 < A*jost a y+B*jostReflected a y) : 0 ≤ A := by
  by_contra hA
  have hA : A < 0 := lt_of_not_ge hA
  have H (y) : 0 ≤ A*(a-1) + (|B| *(a+1))*Real.exp ((-2*a)*y) := by
    have H := mul_pos (hp y) (Real.exp_pos (-a*y))
    rw [add_mul, mul_assoc, jost_scale, mul_assoc, jostReflected_scale] at H
    have H₁ : A*(a-Real.tanh y) ≤ A*(a-1) :=
      mul_le_mul_of_nonpos_left (by linarith [Real.tanh_lt_one y]) hA.le
    have H₂ : B*(Real.exp ((-2*a)*y)*(a+Real.tanh y)) ≤
        (|B| *(a+1))*Real.exp ((-2*a)*y) := by
      calc
        B*(Real.exp ((-2*a)*y)*(a+Real.tanh y)) ≤
            |B| *(Real.exp ((-2*a)*y)*(a+Real.tanh y)) :=
          mul_le_mul_of_nonneg_right (le_abs_self B) (by
            exact mul_nonneg (Real.exp_pos _).le (by linarith [Real.neg_one_lt_tanh y]))
        _ ≤ |B| *(Real.exp ((-2*a)*y)*(a+1)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (by linarith [Real.tanh_lt_one y]) (Real.exp_pos _).le) (abs_nonneg B)
        _ = _ := by ring
    linarith
  have ht : Tendsto (fun y : ℝ => Real.exp ((-2*a)*y)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have hlim : Tendsto (fun y : ℝ => A*(a-1)+(|B| *(a+1))*Real.exp ((-2*a)*y))
      atTop (𝓝 (A*(a-1))) := by simpa using tendsto_const_nhds.add (ht.const_mul (|B| *(a+1)))
  have HH := ge_of_tendsto hlim (Eventually.of_forall H)
  nlinarith

lemma positive_sech_ode_classification {f : ℝ → ℝ} {a : ℝ} (ha : 1 < a)
    (hf : ContDiff ℝ 2 f) (hp : ∀ y, 0 < f y)
    (heq : ∀ y, deriv (deriv f) y = (a^2-2*sech y^2)*f y) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ (0 < A ∨ 0 < B) ∧
      ∀ y, f y = A*jost a y+B*jostReflected a y := by
  have hdet : deriv (jost a) 0 * jostReflected a 0 -
      jost a 0 * deriv (jostReflected a) 0 ≠ 0 := by
    rw [jost_deriv_at_zero, jostReflected_at_zero, jost_at_zero,
      jostReflected_deriv_at_zero]
    have : 0 < (a^2-1)*a-a*-(a^2-1) := by nlinarith
    exact this.ne'
  obtain hrep := ode_basis_expansion hf ((contDiff_jost a).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr (by simp)))
    ((contDiff_jostReflected a).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr (by simp))) heq (jost_ode a) (jostReflected_ode a) hdet
  set A := (deriv f 0 * jostReflected a 0 - f 0 * deriv (jostReflected a) 0) /
      (deriv (jost a) 0 * jostReflected a 0 - jost a 0 * deriv (jostReflected a) 0)
  set B := (deriv (jost a) 0 * f 0 - jost a 0 * deriv f 0) /
      (deriv (jost a) 0 * jostReflected a 0 - jost a 0 * deriv (jostReflected a) 0)
  have hrep' (y) : f y = A*jost a y+B*jostReflected a y := hrep y
  have hA := positive_jost_combination_first_nonneg ha (fun y => by rw [← hrep']; exact hp y)
  have hB := positive_jost_combination_first_nonneg (A := B) (B := A) ha (fun y => by
    have H := hp (-y)
    rw [hrep', jost_reflection] at H
    have hh : jostReflected a (-y) = jost a y := by rw [← jost_reflection, neg_neg]
    rw [hh, add_comm] at H
    exact H)
  refine ⟨A, B, hA, hB, ?_, hrep'⟩
  have H := hp 0
  rw [hrep', jost_at_zero, jostReflected_at_zero] at H
  by_contra hh
  simp only [not_or, not_lt] at hh
  nlinarith

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

lemma laplacian_separated {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (b c x : Space n) :
    Laplacian.laplacian (fun z => Real.exp (inner ℝ b z)*f (inner ℝ c z)) x =
      Real.exp (inner ℝ b x) *
        (deriv (deriv f) (inner ℝ c x)*‖c‖^2 +
          2*deriv f (inner ℝ c x)*inner ℝ b c + f (inner ℝ c x)*‖b‖^2) := by
  have hbi : ContDiff ℝ 2 (fun z : Space n => inner ℝ b z) := (innerSL ℝ b).contDiff
  have hci : ContDiff ℝ 2 (fun z : Space n => inner ℝ c z) := (innerSL ℝ c).contDiff
  have hfd := hf.differentiable (by norm_num)
  have hcomp : ContDiff ℝ 2 (fun z : Space n => f (inner ℝ c z)) := hf.comp hci
  rw [laplacian_fun_mul hbi.exp hcomp,
    laplacian_comp_scalar hci hcomp (fun x => hfd _) (fun x => hf.differentiable_deriv_two _),
    laplacian_exp hbi, gradient_inner, gradient_inner, laplacian_inner, laplacian_inner,
    gradient_comp_inner Real.differentiable_exp, gradient_comp_inner hfd]
  simp only [Real.deriv_exp, real_inner_smul_left, real_inner_smul_right]
  ring

def conePotential {n : ℕ} (ν : Space n) (x : Space n) : ℝ :=
  1 + Real.tanh (inner ℝ ν x / Real.sqrt 2)^2

lemma conePotential_smooth {n : ℕ} (ν : Space n) : ContDiff ℝ ∞ (conePotential ν) := by
  exact contDiff_const.add ((contDiff_tanh.comp ((innerSL ℝ ν).contDiff.div_const _)).pow 2)

lemma conePotential_bounds {n : ℕ} (ν : Space n) (x : Space n) :
    1 ≤ conePotential ν x ∧ conePotential ν x ≤ 2 := by
  dsimp [conePotential]
  constructor
  · nlinarith [sq_nonneg (Real.tanh (inner ℝ ν x / Real.sqrt 2))]
  · linarith [Real.tanh_sq_lt_one (inner ℝ ν x / Real.sqrt 2)]

end DeGiorgi
end

end OAI
