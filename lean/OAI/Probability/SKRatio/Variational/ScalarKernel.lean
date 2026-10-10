import Mathlib

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def m (h : ℝ) : ℝ := tanh h
def v (h : ℝ) : ℝ := 1 - m h ^ 2
def w (h : ℝ) : ℝ := 1 - m h
def kernel (h t : ℝ) : ℝ := v h * v t / (w h + w t)
def g (h : ℝ) : ℝ := v h / (w h + 3/4)
def q (h : ℝ) : ℝ := (w h - 3/4) / (w h + 3/4)
def rho (h : ℝ) : ℝ := (1+m h)*v h/2 - (3/2)*g h^2

lemma m_bounds (h : ℝ) : -1 < m h ∧ m h < 1 :=
  ⟨neg_one_lt_tanh h, tanh_lt_one h⟩
lemma v_pos (h : ℝ) : 0 < v h := sub_pos.mpr (tanh_sq_lt_one h)
lemma v_le_one (h : ℝ) : v h ≤ 1 := by dsimp [v]; nlinarith [sq_nonneg (m h)]
lemma w_pos (h : ℝ) : 0 < w h := sub_pos.mpr (m_bounds h).2
lemma v_factor (h : ℝ) : v h = w h * (1+m h) := by unfold v w; ring
lemma kernel_nonneg (h t : ℝ) : 0 ≤ kernel h t :=
  div_nonneg (mul_nonneg (v_pos h).le (v_pos t).le) (add_pos (w_pos h) (w_pos t)).le
lemma kernel_diag (h : ℝ) : kernel h h = (1+m h)*v h/2 := by
  unfold kernel
  nth_rw 1 [v_factor h]
  have hw := (w_pos h).ne'
  field_simp
  ring

lemma kernel_diag_le_one (h : ℝ) : kernel h h ≤ 1 := by
  rw [kernel_diag]
  have hm := (m_bounds h).2.le
  have hv := v_le_one h
  have hv0 := (v_pos h).le
  nlinarith [(mul_le_mul_of_nonneg_right (show 1+m h ≤ 2 by linarith) hv0)]

lemma kernel_square_le (h t : ℝ) : kernel h t^2 ≤ kernel h h * kernel t t := by
  have ha := w_pos h
  have hb := w_pos t
  have hab : 0 < w h+w t := add_pos ha hb
  unfold kernel
  rw [div_pow,div_mul_div_comm]
  apply (div_le_div_iff₀ (sq_pos_of_pos hab) (mul_pos (add_pos ha ha) (add_pos hb hb))).mpr
  have hh := mul_nonneg (sq_nonneg (v h*v t)) (sq_nonneg (w h-w t))
  nlinarith only [hh]

lemma abs_kernel_le_one (h t : ℝ) : |kernel h t| ≤ 1 := by
  rw [abs_of_nonneg (kernel_nonneg h t)]
  have hs := kernel_square_le h t
  have hd := mul_le_mul (kernel_diag_le_one h) (kernel_diag_le_one t)
    (kernel_nonneg t t) (by norm_num : (0:ℝ) ≤ 1)
  nlinarith [sq_nonneg (kernel h t-1)]

lemma residual_identity (h t : ℝ) :
    kernel h t - (3/2)*g h*g t = kernel h t*q h*q t := by
  have hht := (add_pos (w_pos h) (w_pos t)).ne'
  have hh : w h+3/4 ≠ 0 := by linarith [w_pos h]
  have ht : w t+3/4 ≠ 0 := by linarith [w_pos t]
  unfold kernel g q
  have hh4 : w h*4+3 ≠ 0 := by linarith [w_pos h]
  have ht4 : w t*4+3 ≠ 0 := by linarith [w_pos t]
  field_simp [hht,hh4,ht4]
  ring

lemma rho_eq (h : ℝ) : rho h = kernel h h * q h^2 := by
  have hh := residual_identity h h
  rw [kernel_diag] at hh
  unfold rho
  rw [kernel_diag]
  nlinarith only [hh]

lemma rho_nonneg (h : ℝ) : 0 ≤ rho h := by
  rw [rho_eq]
  exact mul_nonneg (kernel_nonneg h h) (sq_nonneg (q h))

lemma rho_le_one (h : ℝ) : rho h ≤ 1 := by
  have hi := kernel_diag_le_one h
  rw [kernel_diag] at hi
  unfold rho
  nlinarith [sq_nonneg (g h)]

lemma abs_g_le_one (h : ℝ) : |g h| ≤ 1 := by
  have hi := kernel_diag_le_one h
  rw [kernel_diag] at hi
  have hr := rho_nonneg h
  unfold rho at hr
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (g h+1),sq_nonneg (g h-1)]

lemma abs_residual_le (h t : ℝ) :
    |kernel h t - (3/2)*g h*g t| ≤ sqrt (rho h)*sqrt (rho t) := by
  have hs := mul_le_mul_of_nonneg_right (kernel_square_le h t)
    (mul_nonneg (sq_nonneg (q h)) (sq_nonneg (q t)))
  have hsq : (kernel h t - (3/2)*g h*g t)^2 ≤ rho h*rho t := by
    rw [residual_identity,rho_eq h,rho_eq t]
    nlinarith only [hs]
  have hprod : 0 ≤ sqrt (rho h)*sqrt (rho t) := mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  apply (sq_le_sq₀ (abs_nonneg _) hprod).mp
  rw [sq_abs,mul_pow,sq_sqrt (rho_nonneg h),sq_sqrt (rho_nonneg t)]
  exact hsq

lemma continuous_m : Continuous m := by
  unfold m
  simp_rw [tanh_eq_sinh_div_cosh]
  exact Continuous.div Real.continuous_sinh Real.continuous_cosh (fun h => ne_of_gt (Real.cosh_pos h))
lemma continuous_v : Continuous v := continuous_const.sub (continuous_m.pow 2)
lemma continuous_w : Continuous w := continuous_const.sub continuous_m
lemma continuous_g : Continuous g := by
  apply continuous_v.div (continuous_w.add continuous_const)
  intro h
  change w h+3/4 ≠ 0
  linarith [w_pos h]
lemma continuous_kernel : Continuous (Function.uncurry kernel) := by
  apply ((continuous_v.comp continuous_fst).mul (continuous_v.comp continuous_snd)).div
    ((continuous_w.comp continuous_fst).add (continuous_w.comp continuous_snd))
  intro x
  exact (add_pos (w_pos x.1) (w_pos x.2)).ne'
lemma continuous_rho : Continuous rho :=
  (((continuous_const.add continuous_m).mul continuous_v).div_const 2).sub
    ((continuous_g.pow 2).const_mul (3/2))

section Integration
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma memLp_g : MemLp g 2 μ := by
  apply (memLp_const (1:ℝ)).of_le_mul continuous_g.aestronglyMeasurable
    (c := (1:ℝ))
  exact Filter.Eventually.of_forall (fun h => by simpa using abs_g_le_one h)

lemma memLp_sqrt_rho : MemLp (fun h => sqrt (rho h)) 2 μ := by
  apply (memLp_const (1:ℝ)).of_le_mul
    (continuous_sqrt.comp continuous_rho).aestronglyMeasurable (c := (1:ℝ))
  apply Filter.Eventually.of_forall
  intro h
  simp only [Function.comp_apply,Real.norm_eq_abs,abs_one,mul_one,abs_of_nonneg (sqrt_nonneg _)]
  exact (sqrt_le_one).mpr (rho_le_one h)

lemma integrable_rho : Integrable rho μ := by
  exact ((integrable_const (1:ℝ)).mono' continuous_rho.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun h => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (rho_nonneg h)] using rho_le_one h)))

lemma integral_abs_mul_sq_le {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f z : α → ℝ} (hf : MemLp f 2 ν) (hz : MemLp z 2 ν) :
    (∫ x, |f x| *|z x| ∂ν)^2 ≤ (∫ x, f x^2 ∂ν)*(∫ x, z x^2 ∂ν) := by
  have hb := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf) (by simpa using hz)
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs,←Real.sqrt_eq_rpow] at hb
  have ha : 0 ≤ ∫ x, |f x| *|z x| ∂ν := integral_nonneg (fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hs := sq_le_sq₀ ha (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) |>.mpr hb
  simpa only [mul_pow,sq_sqrt (integral_nonneg (fun x => sq_nonneg (f x))),
    sq_sqrt (integral_nonneg (fun x => sq_nonneg (z x)))] using hs

lemma kernel_pair_integrable {b : ℝ → ℝ} (hb : MemLp b 2 μ) :
    Integrable (fun z : ℝ×ℝ => b z.1 * kernel z.1 z.2 * b z.2) (μ.prod μ) := by
  have hI := hb.integrable (by norm_num : (1:ENNReal) ≤ 2)
  apply (hI.norm.mul_prod hI.norm).mono'
    ((hb.aestronglyMeasurable.comp_fst.mul continuous_kernel.aestronglyMeasurable).mul
      hb.aestronglyMeasurable.comp_snd)
  apply Filter.Eventually.of_forall
  intro z
  change |b z.1*kernel z.1 z.2*b z.2| ≤ |b z.1| * |b z.2|
  simp only [abs_mul]
  calc
    |b z.1| *|kernel z.1 z.2| *|b z.2| ≤ |b z.1| *1*|b z.2| := by
      gcongr
      exact abs_kernel_le_one _ _
    _ = |b z.1| *|b z.2| := by ring

theorem kernel_bound {b : ℝ → ℝ} (hb : MemLp b 2 μ) :
    ∫ z : ℝ×ℝ, b z.1*kernel z.1 z.2*b z.2 ∂μ.prod μ ≤
      (3/2)*(∫ h, b h*g h ∂μ)^2 +
        (∫ h, rho h ∂μ)*(∫ h, b h^2 ∂μ) := by
  have hbg : Integrable (fun h => b h*g h) μ := hb.integrable_mul memLp_g
  have hbr : Integrable (fun h => |b h| *sqrt (rho h)) μ :=
    hb.norm.integrable_mul memLp_sqrt_rho
  have hmain := (hbg.mul_prod hbg).const_mul (3/2:ℝ)
  have hrem := hbr.mul_prod hbr
  have him := integral_mono (kernel_pair_integrable hb) (hmain.add hrem)
    (fun z => show b z.1*kernel z.1 z.2*b z.2 ≤
      (3/2)*((b z.1*g z.1)*(b z.2*g z.2)) +
        (|b z.1| *sqrt (rho z.1))*(|b z.2| *sqrt (rho z.2)) from by
      have ha := mul_le_mul_of_nonneg_left (abs_residual_le z.1 z.2)
        (mul_nonneg (abs_nonneg (b z.1)) (abs_nonneg (b z.2)))
      have hh := le_abs_self (b z.1*(kernel z.1 z.2-(3/2)*g z.1*g z.2)*b z.2)
      simp only [abs_mul] at hh
      nlinarith only [ha,hh])
  simp only [Pi.add_apply] at him
  rw [integral_add hmain hrem,integral_const_mul,
    integral_prod_mul (fun h => b h*g h) (fun h => b h*g h),
    integral_prod_mul (fun h => |b h| * sqrt (rho h)) (fun h => |b h| * sqrt (rho h))] at him
  have hcs := integral_abs_mul_sq_le hb (memLp_sqrt_rho (μ := μ))
  simp only [abs_of_nonneg (sqrt_nonneg _),sq_sqrt (rho_nonneg _)] at hcs
  nlinarith only [him,hcs]

omit [IsProbabilityMeasure μ] in
lemma integral_rho_nonneg : 0 ≤ ∫ h, rho h ∂μ := integral_nonneg rho_nonneg

end Integration
end SKRatio.Scalar

end
end

end OAI
