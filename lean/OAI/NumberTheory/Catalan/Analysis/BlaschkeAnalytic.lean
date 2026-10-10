import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import OAI.NumberTheory.Catalan.Estimates.BlaschkeComplex

namespace OAI

noncomputable section
open scoped BigOperators
namespace InternalCatalan

theorem blaschkeFactor_denominator_ne_zero {x : ℝ} {z : ℂ}
    (hx : |x| < 1) (hz : ‖z‖ ≤ 1) : 1 - (x : ℂ) * z ≠ 0 := by
  have hm : ‖(x : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |x| * ‖z‖ ≤ |x| * 1 := mul_le_mul_of_nonneg_left hz (abs_nonneg x)
      _ < 1 := by simpa only [mul_one] using hx
  intro h
  have heq : (x : ℂ) * z = 1 := (sub_eq_zero.mp h).symm
  rw [heq, norm_one] at hm
  exact (lt_irrefl 1) hm

theorem blaschkeFactor_imaginary_denominator_ne_zero (x u : ℝ) :
    1 - (x : ℂ) * (Complex.I * (u : ℂ)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [Complex.mul_re, Complex.mul_im] at hre

theorem blaschkeFactor_imaginary_ne_zero_of_node_ne_zero {x : ℝ}
    (hx : x ≠ 0) (u : ℝ) : blaschkeFactor x (Complex.I * (u : ℂ)) ≠ 0 := by
  unfold blaschkeFactor
  apply div_ne_zero
  · intro h
    have hre : -x = 0 := by
      simpa [Complex.mul_re, Complex.mul_im] using congrArg Complex.re h
    exact hx (neg_eq_zero.mp hre)
  · exact blaschkeFactor_imaginary_denominator_ne_zero x u

theorem blaschkeFactor_analyticAt (x : ℝ) {z : ℂ}
    (hz : 1 - (x : ℂ) * z ≠ 0) : AnalyticAt ℂ (blaschkeFactor x) z := by
  change AnalyticAt ℂ (fun w : ℂ => (w - (x : ℂ)) / (1 - (x : ℂ) * w)) z
  have hid : AnalyticAt ℂ (fun w : ℂ => w) z := analyticAt_id
  have hx : AnalyticAt ℂ (fun _ : ℂ => (x : ℂ)) z := analyticAt_const
  have h1 : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z := analyticAt_const
  exact (hid.sub hx).div (h1.sub (hx.mul hid)) hz

theorem finiteBlaschke_analyticAt {ι : Type*} (s : Finset ι) (x : ι → ℝ) {z : ℂ}
    (hz : ∀ i ∈ s, 1 - (x i : ℂ) * z ≠ 0) :
    AnalyticAt ℂ (finiteBlaschke s x) z := by
  classical
  revert hz
  induction s using Finset.induction_on with
  | empty =>
      intro _
      have hfun : finiteBlaschke (∅ : Finset ι) x = fun _ : ℂ => (1 : ℂ) := by
        funext w
        simp only [finiteBlaschke, Finset.prod_empty]
      rw [hfun]
      exact analyticAt_const
  | @insert i s hi ih =>
      intro hz
      have hhead := blaschkeFactor_analyticAt (x i) (hz i (Finset.mem_insert_self _ _))
      have htail := ih (fun j hj => hz j (Finset.mem_insert_of_mem hj))
      have hfun : finiteBlaschke (insert i s) x =
          fun w => blaschkeFactor (x i) w * finiteBlaschke s x w := by
        funext w
        simp only [finiteBlaschke, Finset.prod_insert hi]
      rw [hfun]
      exact hhead.mul htail

theorem finiteBlaschke_analyticOnNhd_closedDisk {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ s, |x i| < 1) :
    AnalyticOnNhd ℂ (finiteBlaschke s x) (Metric.closedBall (0 : ℂ) 1) := by
  intro z hz
  have hzn : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  exact finiteBlaschke_analyticAt s x
    (fun i hi => blaschkeFactor_denominator_ne_zero (hx i hi) hzn)

theorem finiteBlaschke_imaginary_ne_zero {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ s, x i ≠ 0) (u : ℝ) :
    finiteBlaschke s x (Complex.I * (u : ℂ)) ≠ 0 := by
  unfold finiteBlaschke
  exact Finset.prod_ne_zero_iff.mpr
    (fun i hi => blaschkeFactor_imaginary_ne_zero_of_node_ne_zero (hx i hi) u)

theorem finiteBlaschke_quotient_analyticAt_imaginary {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) (u : ℝ) :
    AnalyticAt ℂ (fun z : ℂ => z ^ D / finiteBlaschke s x z)
      (Complex.I * (u : ℂ)) := by
  have hp : AnalyticAt ℂ (fun z : ℂ => z ^ D) (Complex.I * (u : ℂ)) :=
    analyticAt_id.pow D
  exact hp.div
    (finiteBlaschke_analyticAt s x
      (fun i _ => blaschkeFactor_imaginary_denominator_ne_zero (x i) u))
    (finiteBlaschke_imaginary_ne_zero s x hx u)

theorem finiteBlaschke_quotient_analyticOnNhd_imaginary {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) :
    AnalyticOnNhd ℂ (fun z : ℂ => z ^ D / finiteBlaschke s x z)
      (Set.range (fun u : ℝ => Complex.I * (u : ℂ))) := by
  rintro _ ⟨u, rfl⟩
  exact finiteBlaschke_quotient_analyticAt_imaginary s x D hx u

theorem blaschkeFactor_norm_eq_one {x : ℝ} {z : ℂ}
    (hx : |x| < 1) (hz : ‖z‖ = 1) : ‖blaschkeFactor x z‖ = 1 := by
  have hzsq : Complex.normSq z = 1 := by
    rw [← Complex.sq_norm, hz]
    norm_num
  have hid : Complex.normSq (z - (x : ℂ)) - Complex.normSq (1 - (x : ℂ) * z) =
      (1 - x ^ 2) * (Complex.normSq z - 1) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, zero_mul, add_zero,
      sub_zero, zero_sub]
    ring
  rw [hzsq, sub_self, mul_zero] at hid
  have hsq := sub_eq_zero.mp hid
  have hnorm : ‖z - (x : ℂ)‖ = ‖1 - (x : ℂ) * z‖ := by
    simpa only [Complex.norm_def] using congrArg Real.sqrt hsq
  change ‖(z - (x : ℂ)) / (1 - (x : ℂ) * z)‖ = 1
  rw [norm_div, hnorm]
  exact div_self (norm_ne_zero_iff.mpr (blaschkeFactor_denominator_ne_zero hx hz.le))

theorem finiteBlaschke_norm_eq_one {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ s, |x i| < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖finiteBlaschke s x z‖ = 1 := by
  rw [finiteBlaschke_norm]
  apply Finset.prod_eq_one
  intro i hi
  exact blaschkeFactor_norm_eq_one (hx i hi) hz

theorem finiteBlaschke_eval_node {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {i : ι} (hi : i ∈ s) : finiteBlaschke s x (x i : ℂ) = 0 := by
  unfold finiteBlaschke
  apply Finset.prod_eq_zero hi
  simp only [blaschkeFactor, sub_self, zero_div]

end InternalCatalan

end

end OAI
