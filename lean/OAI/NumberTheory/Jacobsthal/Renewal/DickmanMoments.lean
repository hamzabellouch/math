import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import OAI.NumberTheory.Jacobsthal.Analysis.WeightFutureIntegrals

namespace OAI

namespace Erdos970

section

open Set Filter MeasureTheory
open scoped Topology
namespace Erdos970Dependency.StandardBoundary
open NumberTheoryLean.Dickman NumberTheoryLean.DickmanDecay

theorem rho_exp_bound {x : ℝ} (hx : 0 ≤ x) : rho x ≤ Real.exp 2 * Real.exp (-x) := by
  have hle (y : ℝ) (hy : 0 ≤ y) : rho y ≤ 1 := by
    simpa only [rho_initial (by norm_num : (0:ℝ) ≤ 1)] using rho_antitone hy
  by_cases h2 : 2 ≤ x
  · have h := rho_exponential_comparison 2 1 2 x le_rfl
      (fun t ht => hazard_ge_one ht) le_rfl h2
    have h' := mul_le_mul_of_nonneg_right (hle 2 (by norm_num)) (Real.exp_pos (-(1:ℝ)*(x-2))).le
    have he : Real.exp (-(1:ℝ)*(x-2)) = Real.exp 2 * Real.exp (-x) := by
      rw [← Real.exp_add]; congr 1; ring
    simpa only [one_mul, he] using h.trans h'
  · apply (hle x hx).trans
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith)

theorem rho_moment_integrable (n : ℕ) :
    IntegrableOn (fun x : ℝ => x^n*rho x) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => x^n*Real.exp (-x)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1)
      (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) (by norm_num : (0:ℝ)<1)
    simpa only [Real.rpow_natCast,Real.rpow_one,neg_one_mul] using! h
  apply (hg.const_mul (Real.exp 2)).mono'
    (((continuous_id.pow n).mul rho_continuous).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := le_of_lt hx
  change ‖x^n*rho x‖ ≤ Real.exp 2*(x^n*Real.exp (-x))
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hx0 n),abs_of_nonneg (rho_nonneg x)]
  calc
    _ ≤ x^n*(Real.exp 2*Real.exp (-x)) := mul_le_mul_of_nonneg_left (rho_exp_bound hx0) (pow_nonneg hx0 n)
    _ = Real.exp 2*(x^n*Real.exp (-x)) := by ring

theorem rho_moment_tendsto_zero (n : ℕ) :
    Tendsto (fun x : ℝ => x^n*rho x) atTop (𝓝 0) := by
  have hl := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).const_mul (Real.exp 2)
  simp only [mul_zero] at hl
  apply squeeze_zero' ?_ ?_ hl
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    exact mul_nonneg (pow_nonneg hx n) (rho_nonneg x)
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    calc
      _ ≤ x^n*(Real.exp 2*Real.exp (-x)) := mul_le_mul_of_nonneg_left (rho_exp_bound hx) (pow_nonneg hx n)
      _ = Real.exp 2*(x^n*Real.exp (-x)) := by ring

theorem halfline_shift (a b : ℝ) (g : ℝ → ℝ) :
    ((∫ x in Ioi (a+b),g x) = ∫ x in Ioi a,g (x+b)) ∧
    (IntegrableOn g (Ioi (a+b)) ↔ IntegrableOn (fun x => g (x+b)) (Ioi a)) := by
  have hd : ∀ x ∈ Ioi a, HasDerivWithinAt (fun y : ℝ => y+b) 1 (Ioi a) x :=
    fun x _ => ((hasDerivAt_id x).add_const b).hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ => y+b) (Ioi a) := fun x _ y _ h => by linarith
  have him : (fun y : ℝ => y+b) '' Ioi a = Ioi (a+b) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; change a < y at hy; change a+b < y+b; linarith
    · intro hx; refine ⟨x-b,?_,by ring⟩; change a+b < x at hx; change a < x-b; linarith
  constructor
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj g
    simpa only [him,abs_one,one_smul] using h
  · have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd hinj g
    simpa only [him,abs_one,one_smul] using h

end Erdos970Dependency.StandardBoundary

end

section

open Set Filter MeasureTheory
open scoped Topology
namespace Erdos970Dependency.StandardBoundary
open NumberTheoryLean.Dickman NumberTheoryLean.DickmanDecay

theorem rho_quotient_integral :
    IntegrableOn (fun y : ℝ => rho y/(y+1)) (Ioi 0) ∧
    (∫ y in Ioi 0,rho y/(y+1)) = 1 := by
  have hc : Continuous (fun y : ℝ => rho (y+1)) := rho_continuous.comp (continuous_id.add continuous_const)
  have hd : ∀ y ∈ Ioi (0:ℝ), HasDerivAt (fun x : ℝ => rho (x+1)) (-(rho y/(y+1))) y := by
    intro y hy
    have hh := (rho_hasDerivAt (u := y+1) (by change 0 < y at hy; linarith)).comp y ((hasDerivAt_id y).add_const 1)
    simpa only [add_sub_cancel_right,mul_one,neg_div] using! hh
  have hn : ∀ y ∈ Ioi (0:ℝ), -(rho y/(y+1)) ≤ 0 := by
    intro y hy
    exact neg_nonpos.mpr (div_nonneg (rho_nonneg y) (by change 0 < y at hy; linarith))
  have hl : Tendsto (fun x : ℝ => rho (x+1)) atTop (𝓝 0) :=
    rho_tendsto_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  have hi := integrableOn_Ioi_deriv_of_nonpos hc.continuousWithinAt hd hn hl
  have he := integral_Ioi_of_hasDerivAt_of_nonpos hc.continuousWithinAt hd hn hl
  refine ⟨integrable_neg_iff.mp hi,?_⟩
  simp only [integral_neg,zero_add,rho_initial le_rfl,zero_sub] at he
  linarith

theorem rho_first_moment :
    (∫ y in Ioi 0,y*rho y) = ∫ y in Ioi 0,rho y := by
  have h0 : IntegrableOn rho (Ioi 0) := by simpa only [pow_zero,one_mul] using rho_moment_integrable 0
  have h1 : IntegrableOn (fun y : ℝ => y*rho y) (Ioi 0) := by simpa only [pow_one] using rho_moment_integrable 1
  have h1tail := h1.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have hadd : IntegrableOn (fun y : ℝ => (y+1)*rho y) (Ioi 0) := by
    apply (h1.add h0).congr_fun _ measurableSet_Ioi
    intro y _
    change y*rho y+rho y = (y+1)*rho y
    ring
  have hshift := halfline_shift 1 (-1) (fun y : ℝ => (y+1)*rho y)
  simp only [← sub_eq_add_neg,sub_add_cancel,sub_self] at hshift
  have hst : IntegrableOn (fun y : ℝ => y*rho (y-1)) (Ioi 1) := by
    exact hshift.2.mp hadd
  have hseq : (∫ y in Ioi 1,y*rho (y-1)) =
      (∫ y in Ioi 0,y*rho y)+(∫ y in Ioi 0,rho y) := by
    have hp (y : ℝ) : (y+1)*rho y = y*rho y+rho y := by ring
    simpa only [hp,integral_add h1 h0] using hshift.1.symm
  have hder : ∀ y ∈ Ioi (1:ℝ), HasDerivAt (fun x : ℝ => x^2*rho x)
      (2*y*rho y-y*rho (y-1)) y := by
    intro y hy
    have hd := ((hasDerivAt_id y).pow 2).mul (rho_hasDerivAt hy)
    change HasDerivAt (fun x : ℝ => x^2*rho x) (2*y^1*1*rho y+y^2*(-rho (y-1)/y)) y at hd
    convert! hd using 1
    have hy0 : y ≠ 0 := by change 1 < y at hy; linarith
    field_simp
    ring
  have hint : IntegrableOn (fun y : ℝ => 2*y*rho y-y*rho (y-1)) (Ioi 1) := by
    have hh : IntegrableOn (fun y : ℝ => 2*(y*rho y)-y*rho (y-1)) (Ioi 1) :=
      (h1tail.const_mul 2).sub hst
    apply hh.congr_fun _ measurableSet_Ioi
    intro y _
    dsimp only
    ring
  have hcont : Continuous (fun x : ℝ => x^2*rho x) := (continuous_id.pow 2).mul rho_continuous
  have he := integral_Ioi_of_hasDerivAt_of_tendsto
    hcont.continuousWithinAt hder hint (rho_moment_tendsto_zero 2)
  have hp (y : ℝ) : 2*y*rho y-y*rho (y-1)=2*(y*rho y)-y*rho (y-1) := by ring
  simp only [hp,integral_sub (h1tail.const_mul 2) hst,integral_const_mul,
    one_pow,rho_initial le_rfl,one_mul,zero_sub,hseq] at he
  have hunit : (∫ y : ℝ in 0..1,y*rho y) = (1:ℝ)/2 := by
    calc
      _ = ∫ y : ℝ in 0..1,y := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hy
        change y*rho y = y
        rw [rho_initial hy.2,mul_one]
      _ = _ := by norm_num
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi h1 (by norm_num : (0:ℝ) ≤ 1)
  rw [hunit] at hsplit
  linarith

theorem rho_quadratic_quotient :
    IntegrableOn (fun y : ℝ => y^2*rho y/(y+1)) (Ioi 0) ∧
    (∫ y in Ioi 0,y^2*rho y/(y+1)) = 1 := by
  have h0 : IntegrableOn rho (Ioi 0) := by simpa only [pow_zero,one_mul] using rho_moment_integrable 0
  have h1 : IntegrableOn (fun y : ℝ => y*rho y) (Ioi 0) := by simpa only [pow_one] using rho_moment_integrable 1
  have heq : EqOn (fun y : ℝ => y^2*rho y/(y+1))
      (fun y => y*rho y-rho y+rho y/(y+1)) (Ioi 0) := by
    intro y hy
    have hn : y+1 ≠ 0 := by change 0 < y at hy; linarith
    field_simp
    ring
  refine ⟨((h1.sub h0).add rho_quotient_integral.1).congr_fun (fun y hy => (heq hy).symm) measurableSet_Ioi,?_⟩
  have hs : IntegrableOn (fun y : ℝ => y*rho y-rho y) (Ioi 0) := h1.sub h0
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
    integral_add hs rho_quotient_integral.1,integral_sub h1 h0,
    rho_first_moment,rho_quotient_integral.2]
  ring

end Erdos970Dependency.StandardBoundary

end

end Erdos970

end OAI
