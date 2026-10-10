import Mathlib

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ParametrixUniqueness
variable {V : Type} [NormedAddCommGroup V]

def radius (x : V) : ℝ := Real.sqrt (1+‖x‖^2)
def weight (x : V) : ℝ := Real.exp (-Real.sqrt (1+‖x‖^2))

lemma radius_pos (x : V) : 0 < radius x := by
  exact Real.sqrt_pos.2 (by positivity)
lemma radius_sq (x : V) : radius x ^ 2 = 1+‖x‖^2 := by
  exact Real.sq_sqrt (by positivity)
lemma radius_one_le (x : V) : 1 ≤ radius x := by
  have := radius_sq x
  have := radius_pos x
  nlinarith
lemma norm_le_radius (x : V) : ‖x‖ ≤ radius x := by
  have := radius_sq x
  have := radius_pos x
  nlinarith [norm_nonneg x]
lemma weight_pos (x : V) : 0 < weight x := Real.exp_pos _
variable [InnerProductSpace ℝ V]

lemma contDiff_radius (n : ℕ∞ω) : ContDiff ℝ n (radius : V → ℝ) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun x => by positivity)
lemma contDiff_weight (n : ℕ∞ω) : ContDiff ℝ n (weight : V → ℝ) :=
  (contDiff_radius n).neg.exp

lemma hasFDerivAt_radius (x : V) : HasFDerivAt radius
    ((radius x)⁻¹ • innerSL ℝ x) x := by
  have h := ((hasFDerivAt_const (1:ℝ) x).add (hasFDerivAt_id x).norm_sq).sqrt
    (by positivity : (1:ℝ)+‖x‖^2 ≠ 0)
  convert h using 1 <;> ext v <;> simp [radius,div_eq_mul_inv]
  ring

lemma hasFDerivAt_weight (x : V) : HasFDerivAt weight
    ((-weight x / radius x) • innerSL ℝ x) x := by
  have h := (hasFDerivAt_radius x).neg.exp
  convert h using 1 <;> ext v <;> simp [weight,radius,div_eq_mul_inv]
  ring

lemma norm_fderiv_weight_le (x : V) : ‖fderiv ℝ weight x‖ ≤ weight x := by
  rw [(hasFDerivAt_weight x).fderiv,norm_smul,innerSL_apply_norm]
  rw [Real.norm_eq_abs,abs_div,abs_neg,abs_of_pos (weight_pos x),
    abs_of_pos (radius_pos x)]
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (radius_pos x)).2
    (mul_le_mul_of_nonneg_left (norm_le_radius x) (weight_pos x).le)

def dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : V) (f : V → E) (x : V) : E := fderiv ℝ f x v

lemma contDiff_dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : V) (f : V → E) {n : ℕ∞ω} (hf : ContDiff ℝ (n+1) f) :
    ContDiff ℝ n (dir v f) :=
  (hf.fderiv_right le_rfl).clm_apply contDiff_const

def radialComponent (v x : V) : ℝ := inner ℝ v x / radius x

lemma contDiff_radialComponent (v : V) (n : ℕ∞ω) :
    ContDiff ℝ n (radialComponent v : V → ℝ) :=
  (innerSL ℝ v).contDiff.div (contDiff_radius n) (fun x => (radius_pos x).ne')

lemma radialComponent_bound (v x : V) : |radialComponent v x| ≤ ‖v‖ := by
  rw [radialComponent,abs_div,abs_of_pos (radius_pos x)]
  apply (div_le_iff₀ (radius_pos x)).2
  have hi : |inner ℝ v x| ≤ ‖v‖ * ‖x‖ := by
    simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) v x
  exact hi.trans (mul_le_mul_of_nonneg_left (norm_le_radius x) (norm_nonneg v))

lemma dir_radialComponent (v x : V) :
    dir v (radialComponent v) x = (‖v‖^2 - radialComponent v x ^ 2) / radius x := by
  have h := (innerSL ℝ v).hasFDerivAt.mul
    ((hasDerivAt_inv (radius_pos x).ne').comp_hasFDerivAt x (hasFDerivAt_radius x))
  have he : radialComponent v = fun y => inner ℝ v y * (radius y)⁻¹ := by
    funext y; simp [radialComponent,div_eq_mul_inv]
  change HasFDerivAt (fun y => inner ℝ v y * (radius y)⁻¹) _ x at h
  rw [dir,he,h.fderiv]
  simp only [add_apply,smul_apply,
    innerSL_apply_apply,smul_eq_mul,real_inner_self_eq_norm_sq]
  rw [real_inner_comm v x]
  dsimp [radialComponent]
  field_simp [(radius_pos x).ne']
  ring

lemma dir_weight (v x : V) : dir v weight x = -weight x * radialComponent v x := by
  rw [dir,(hasFDerivAt_weight x).fderiv]
  simp only [smul_apply,smul_eq_mul,innerSL_apply_apply]
  rw [real_inner_comm v x]
  dsimp [radialComponent]
  ring

lemma dir_dir_weight (v x : V) : dir v (dir v weight) x =
    weight x * (radialComponent v x ^ 2 -
      (‖v‖^2-radialComponent v x ^ 2) / radius x) := by
  have he : dir v weight = fun y => -weight y * radialComponent v y :=
    funext (dir_weight v)
  rw [he,dir,fderiv_fun_mul
    ((contDiff_weight 1).neg.differentiable (by norm_num)).differentiableAt
    ((contDiff_radialComponent v 1).differentiable (by norm_num)).differentiableAt]
  simp only [add_apply,smul_apply,smul_eq_mul]
  rw [fderiv_fun_neg]
  change -weight x * dir v (radialComponent v) x + radialComponent v x * -dir v weight x = _
  rw [dir_radialComponent,dir_weight]
  ring

lemma dir_dir_weight_bound (v x : V) :
    |dir v (dir v weight) x| ≤ weight x * ‖v‖^2 := by
  have hq : radialComponent v x ^ 2 ≤ ‖v‖^2 := by
    simpa only [sq_abs] using sq_le_sq₀ (abs_nonneg _) (norm_nonneg v) |>.2
      (radialComponent_bound v x)
  have hd : 0 ≤ (‖v‖^2-radialComponent v x^2) / radius x :=
    div_nonneg (sub_nonneg.mpr hq) (radius_pos x).le
  have hd' : (‖v‖^2-radialComponent v x^2) / radius x ≤ ‖v‖^2 := by
    apply (div_le_iff₀ (radius_pos x)).2
    nlinarith [radius_one_le x,sq_nonneg (radialComponent v x),
      mul_le_mul_of_nonneg_left (radius_one_le x) (sq_nonneg ‖v‖)]
  rw [dir_dir_weight,abs_mul,abs_of_pos (weight_pos x)]
  apply mul_le_mul_of_nonneg_left _ (weight_pos x).le
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (radialComponent v x)]

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma integrable_weight : Integrable (weight : V → ℝ) := by
  let n := Module.finrank ℝ V + 1
  have hn : (Module.finrank ℝ V : ℝ) < (n:ℝ) := by dsimp [n]; simp
  have hint := (integrable_rpow_neg_one_add_norm_sq (μ := volume) hn).const_mul
    (n.factorial : ℝ)
  apply hint.mono' (contDiff_weight 0).continuous.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_pos (weight_pos x)]
  have hr := radius_pos x
  have hnfac : (0:ℝ)<n.factorial := by positivity
  have he := Real.pow_div_factorial_le_exp (radius x) hr.le n
  have hp : (1+‖x‖^2) ^ (-(n:ℝ)/2) = (radius x ^ n)⁻¹ := by
    rw [show -(n:ℝ)/2 = -((1/2:ℝ)*n) by ring,Real.rpow_neg (by positivity),
      Real.rpow_mul (by positivity),←Real.sqrt_eq_rpow,Real.rpow_natCast]
    rfl
  rw [hp]
  change Real.exp (-radius x) ≤ _
  rw [Real.exp_neg]
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).2
  have hp0 : 0 < radius x ^ n := pow_pos hr _
  have hh := (div_le_iff₀ hnfac).1 he
  rw [←div_eq_mul_inv,div_mul_eq_mul_div]
  apply (le_div_iff₀ hp0).2
  simpa [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
end ParametrixUniqueness

end

end OAI
