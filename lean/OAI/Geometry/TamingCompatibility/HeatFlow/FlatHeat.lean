import Mathlib

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
open MeasureTheory Set
open scoped RealInnerProductSpace ContDiff
abbrev V := EuclideanSpace ℝ (Fin 4)

def heat (t : ℝ) (z : V) : ℝ :=
  (4*Real.pi*t)⁻¹^2 * Real.exp (-‖z‖^2/(4*t))

lemma heat_pos {t : ℝ} (ht : 0 < t) (z : V) : 0 < heat t z := by
  unfold heat
  positivity

lemma heat_nonneg (t : ℝ) (z : V) : 0 ≤ heat t z := by
  unfold heat
  positivity

lemma heat_neg (t : ℝ) (z : V) : heat t (-z) = heat t z := by
  simp [heat]

lemma heat_continuous (t : ℝ) : Continuous (heat t) := by
  unfold heat
  fun_prop

lemma gaussian_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : V => Real.exp (-b*‖z‖^2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := V) (b := (b:ℂ)) hb 0 0).norm
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using h

lemma gaussian_integral {b : ℝ} (hb : 0 < b) :
    (∫ z : V, Real.exp (-b*‖z‖^2)) = (Real.pi/b)^2 := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := V) hb
  norm_num only [finrank_euclideanSpace, Fintype.card_fin, show (4:ℝ)/2 = 2 by norm_num,
    Real.rpow_natCast] at h
  simpa only [Real.rpow_ofNat] using h

lemma heat_integrable {t : ℝ} (ht : 0 < t) : Integrable (heat t) := by
  have h := (gaussian_integrable (show 0 < 1/(4*t) by positivity)).const_mul ((4*Real.pi*t)⁻¹^2)
  convert h using 1
  funext z
  unfold heat
  congr 2
  ring

lemma heat_integral {t : ℝ} (ht : 0 < t) : (∫ z : V, heat t z) = 1 := by
  have he : heat t = fun z : V => (4*Real.pi*t)⁻¹^2 * Real.exp (-(1/(4*t))*‖z‖^2) := by
    funext z
    unfold heat
    congr 2
    ring
  rw [he, integral_const_mul, gaussian_integral (by positivity)]
  field_simp

lemma heat_scale {r : ℝ} (hr : 0 < r) (t : ℝ) (z : V) :
    heat (r^2*t) (r • z) = (r⁻¹)^4 * heat t z := by
  simp only [heat, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow]
  have he : -(r^2*‖z‖^2)/(4*(r^2*t)) = -‖z‖^2/(4*t) := by field_simp
  rw [he]
  ring

lemma heat_diagonal {t : ℝ} : heat t 0 = (4*Real.pi*t)⁻¹^2 := by
  simp [heat]

lemma heat_contDiff (t : ℝ) : ContDiff ℝ ∞ (heat t) := by
  exact contDiff_const.mul (((contDiff_id.norm_sq (𝕜 := ℝ)).neg.div_const (4*t)).exp)

lemma heat_hasFDerivAt (t : ℝ) (z : V) :
    HasFDerivAt (heat t) ((-heat t z/(2*t)) • innerSL ℝ z) z := by
  have h := ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.neg.mul_const (4*t)⁻¹).exp).const_mul
    ((4*Real.pi*t)⁻¹^2))
  convert! h using 1
  ext w
  simp only [heat, smul_apply, neg_apply,
    smul_eq_mul, innerSL_apply_apply, Pi.neg_apply]
  ring_nf

lemma heat_fderiv (t : ℝ) (z w : V) :
    fderiv ℝ (heat t) z w = -heat t z/(2*t) * ⟪z,w⟫ := by
  rw [(heat_hasFDerivAt t z).fderiv]
  rfl

lemma heat_hasDerivAt_time {t : ℝ} (ht : 0 < t) (z : V) :
    HasDerivAt (fun s => heat s z) ((-2/t+‖z‖^2/(4*t^2))*heat t z) t := by
  have hc : HasDerivAt (fun s : ℝ => 4*Real.pi*s) (4*Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (4*Real.pi)
  have hi := (hc.inv (by positivity)).pow 2
  have hd := (hasDerivAt_const t (-‖z‖^2)).div
    ((hasDerivAt_id t).const_mul 4) (by positivity)
  have h := hi.mul hd.exp
  convert! h using 1
  dsimp only [heat, Pi.inv_apply, Pi.pow_apply, Pi.div_apply, Pi.mul_apply, id_eq]
  field_simp [ne_of_gt ht, Real.pi_ne_zero]
  ring_nf
  field_simp [ne_of_gt ht, Real.pi_ne_zero]

lemma heat_directional_hasFDerivAt (t : ℝ) (z v : V) :
    HasFDerivAt (fun y => fderiv ℝ (heat t) y v)
      ((heat t z * ⟪z,v⟫/(4*t^2)) • innerSL ℝ z -
        (heat t z/(2*t)) • innerSL ℝ v) z := by
  have hlin : HasFDerivAt (fun y : V => ⟪y,v⟫) (innerSL ℝ v) z := by
    convert! (innerSL ℝ v).hasFDerivAt (x := z) using 1
    ext y
    exact real_inner_comm v y
  have h := ((heat_hasFDerivAt t z).neg.mul_const (2*t)⁻¹).mul hlin
  have he : (fun y => fderiv ℝ (heat t) y v) =
      (fun y => -heat t y*(2*t)⁻¹ * ⟪y,v⟫) := by
    funext y
    rw [heat_fderiv]
    ring
  rw [he]
  convert! h using 1
  ext u
  simp only [sub_apply, smul_apply, innerSL_apply_apply, add_apply, neg_apply,
    smul_eq_mul, Pi.neg_apply]
  ring

lemma heat_hessian (t : ℝ) (z u v : V) :
    fderiv ℝ (fun y => fderiv ℝ (heat t) y v) z u =
      heat t z * (⟪z,u⟫*⟪z,v⟫/(4*t^2) - ⟪u,v⟫/(2*t)) := by
  rw [(heat_directional_hasFDerivAt t z v).fderiv]
  simp only [sub_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_comm (y := v)]
  ring

lemma gaussian_complete_square {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (x y z : V) :
    ‖x-z‖^2/t + ‖z-y‖^2/s = ‖x-y‖^2/(t+s) +
      ‖z - ((s/(t+s)) • x + (t/(t+s)) • y)‖^2/(t*s/(t+s)) := by
  have hxz : ⟪z,x⟫ = ⟪x,z⟫ := real_inner_comm x z
  have hxy : ⟪y,x⟫ = ⟪x,y⟫ := real_inner_comm x y
  have hyz : ⟪z,y⟫ = ⟪y,z⟫ := real_inner_comm y z
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hxz, hxy, hyz]
  field_simp
  ring

lemma heat_product {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (x y z : V) :
    heat t (x-z) * heat s (z-y) =
      heat (t+s) (x-y) * heat (t*s/(t+s))
        (z - ((s/(t+s)) • x + (t/(t+s)) • y)) := by
  have ha : (4*Real.pi*t)⁻¹^2 * (4*Real.pi*s)⁻¹^2 =
      (4*Real.pi*(t+s))⁻¹^2 * (4*Real.pi*(t*s/(t+s)))⁻¹^2 := by
    field_simp
  have he : Real.exp (-‖x-z‖^2/(4*t)) * Real.exp (-‖z-y‖^2/(4*s)) =
      Real.exp (-‖x-y‖^2/(4*(t+s))) * Real.exp
        (-‖z - ((s/(t+s)) • x + (t/(t+s)) • y)‖^2/(4*(t*s/(t+s)))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have h := gaussian_complete_square ht hs x y z
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv] at h ⊢
    linear_combination -(1/4 : ℝ) * h
  unfold heat
  calc
    _ = ((4*Real.pi*t)⁻¹^2 * (4*Real.pi*s)⁻¹^2) *
        (Real.exp (-‖x-z‖^2/(4*t)) * Real.exp (-‖z-y‖^2/(4*s))) := by ring
    _ = _ := by rw [ha, he]; ring

lemma heat_convolution_integrable {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (x y : V) :
    Integrable (fun z => heat t (x-z) * heat s (z-y)) := by
  simp_rw [heat_product ht hs]
  exact ((heat_integrable (show 0 < t*s/(t+s) by positivity)).comp_sub_right _).const_mul _

lemma heat_convolution {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (x y : V) :
    (∫ z : V, heat t (x-z) * heat s (z-y)) = heat (t+s) (x-y) := by
  simp_rw [heat_product ht hs]
  rw [integral_const_mul, integral_sub_right_eq_self, heat_integral (by positivity), mul_one]

def laplacian (f : V → ℝ) (x : V) : ℝ :=
  ∑ i : Fin 4, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.basisFun (Fin 4) ℝ i)) x
    (EuclideanSpace.basisFun (Fin 4) ℝ i)

lemma heat_equation {t : ℝ} (ht : 0 < t) (z : V) :
    deriv (fun s => heat s z) t = laplacian (heat t) z := by
  rw [(heat_hasDerivAt_time ht z).deriv]
  unfold laplacian
  simp only [heat_hessian, OrthonormalBasis.inner_eq_one, ← pow_two]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div,
    (EuclideanSpace.basisFun (Fin 4) ℝ).sum_sq_inner_left z]
  norm_num
  ring

lemma gaussian_weight_absorption {t : ℝ} (ht : 0 < t) (z : V) (n : ℕ) :
    ‖z‖^(2*n) * heat t z ≤ 4 * (8*t)^n * (n.factorial : ℝ) * heat (2*t) z := by
  let a : ℝ := ‖z‖^2/(8*t)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have h := Real.pow_div_factorial_le_exp a ha n
  have hf : 0 < (n.factorial : ℝ) := by positivity
  have h1 : a^n * Real.exp (-a) ≤ (n.factorial : ℝ) := by
    calc
      _ ≤ ((n.factorial : ℝ) * Real.exp a) * Real.exp (-a) :=
        mul_le_mul_of_nonneg_right (by nlinarith [(div_le_iff₀ hf).mp h]) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; simp
  have hz : ‖z‖^(2*n) = (8*t)^n*a^n := by
    rw [← mul_pow, pow_mul]
    congr 1
    dsimp [a]
    field_simp
  have hH : heat t z = 4 * heat (2*t) z * Real.exp (-a) := by
    have hp : (4*Real.pi*t)⁻¹^2 = 4*(4*Real.pi*(2*t))⁻¹^2 := by field_simp; ring
    have he : -‖z‖^2/(4*t) = -a + -a := by dsimp [a]; ring
    have he2 : -‖z‖^2/(4*(2*t)) = -a := by dsimp [a]; ring
    unfold heat
    rw [hp, he, he2, Real.exp_add]
    ring
  have hp := heat_nonneg (2*t) z
  rw [hz, hH]
  calc
    _ = (4*(8*t)^n*heat (2*t) z) * (a^n*Real.exp (-a)) := by ring
    _ ≤ (4*(8*t)^n*heat (2*t) z) * (n.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

lemma heat_gradient_bound {t : ℝ} (ht : 0 < t) (z v : V) :
    |fderiv ℝ (heat t) z v| ≤ heat t z * (‖z‖*‖v‖/(2*t)) := by
  rw [heat_fderiv, abs_mul, abs_div, abs_neg, abs_of_nonneg (heat_nonneg t z),
    abs_of_pos (show 0 < 2*t by positivity)]
  calc
    _ ≤ (heat t z/(2*t)) * (‖z‖*‖v‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm z v)
        (div_nonneg (heat_nonneg t z) (by positivity))
    _ = _ := by ring

lemma heat_hessian_bound {t : ℝ} (ht : 0 < t) (z u v : V) :
    |fderiv ℝ (fun y => fderiv ℝ (heat t) y v) z u| ≤
      heat t z * (‖z‖^2/(4*t^2) + 1/(2*t)) * ‖u‖*‖v‖ := by
  rw [heat_hessian, abs_mul, abs_of_nonneg (heat_nonneg t z)]
  have h1 : |⟪z,u⟫*⟪z,v⟫/(4*t^2)| ≤ ‖z‖^2*‖u‖*‖v‖/(4*t^2) := by
    rw [abs_div, abs_mul, abs_of_pos (show 0 < 4*t^2 by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ (‖z‖*‖u‖)*(‖z‖*‖v‖) :=
        mul_le_mul (abs_real_inner_le_norm z u) (abs_real_inner_le_norm z v)
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have h2 : |⟪u,v⟫/(2*t)| ≤ ‖u‖*‖v‖/(2*t) := by
    rw [abs_div, abs_of_pos (show 0 < 2*t by positivity)]
    exact div_le_div_of_nonneg_right (abs_real_inner_le_norm u v) (by positivity)
  calc
    _ ≤ heat t z * (|⟪z,u⟫*⟪z,v⟫/(4*t^2)| + |⟪u,v⟫/(2*t)|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (heat_nonneg t z)
    _ ≤ heat t z * (‖z‖^2*‖u‖*‖v‖/(4*t^2) + ‖u‖*‖v‖/(2*t)) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) (heat_nonneg t z)
    _ = _ := by ring

lemma normal_jet_gradient_bound {t : ℝ} (ht : 0 < t) (z v : V) :
    ‖z‖ * |fderiv ℝ (heat t) z v| ≤ 16 * heat (2*t) z * ‖v‖ := by
  have h := gaussian_weight_absorption ht z 1
  norm_num only [Nat.factorial_one, Nat.mul_one, pow_one, mul_one] at h
  calc
    _ ≤ ‖z‖ * (heat t z * (‖z‖*‖v‖/(2*t))) :=
      mul_le_mul_of_nonneg_left (heat_gradient_bound ht z v) (norm_nonneg _)
    _ = (‖z‖^2 * heat t z) * (‖v‖/(2*t)) := by ring
    _ ≤ (4*(8*t)*heat (2*t) z) * (‖v‖/(2*t)) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by field_simp; ring

lemma normal_jet_hessian_bound {t : ℝ} (ht : 0 < t) (z u v : V) :
    ‖z‖^2 * |fderiv ℝ (fun y => fderiv ℝ (heat t) y v) z u| ≤
      144 * heat (2*t) z * ‖u‖*‖v‖ := by
  have h1 := gaussian_weight_absorption ht z 1
  have h2 := gaussian_weight_absorption ht z 2
  norm_num only [Nat.factorial_one, Nat.mul_one, pow_one, mul_one] at h1
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat] at h2
  calc
    _ ≤ ‖z‖^2 * (heat t z * (‖z‖^2/(4*t^2) + 1/(2*t)) * ‖u‖*‖v‖) :=
      mul_le_mul_of_nonneg_left (heat_hessian_bound ht z u v) (sq_nonneg _)
    _ = ((‖z‖^4*heat t z)/(4*t^2) + (‖z‖^2*heat t z)/(2*t)) * ‖u‖*‖v‖ := by ring
    _ ≤ ((4*(8*t)^2*2*heat (2*t) z)/(4*t^2) +
        (4*(8*t)*heat (2*t) z)/(2*t)) * ‖u‖*‖v‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact add_le_add (div_le_div_of_nonneg_right h2 (by positivity))
        (div_le_div_of_nonneg_right h1 (by positivity))
    _ = _ := by field_simp; ring

end TamingCompatibility.GeometricHilbert.FlatHeat

end

end OAI
