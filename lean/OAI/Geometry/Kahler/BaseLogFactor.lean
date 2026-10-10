import OAI.Geometry.Kahler.BaseCircleLog

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

def logFactor (q ε : ℝ) : ℝ :=
  (1+q^2+ε^2+Real.sqrt ((1+q^2+ε^2)^2-4*q^2))/2

lemma logFactor_discriminant (q ε : ℝ) :
    (1-q^2)^2 ≤ (1+q^2+ε^2)^2-4*q^2 := by
  nlinarith [sq_nonneg ε,mul_nonneg (sq_nonneg ε) (sq_nonneg q),sq_nonneg (ε^2)]

lemma logFactor_one_le (q ε : ℝ) : 1 ≤ logFactor q ε := by
  have hh := Real.sqrt_le_sqrt (logFactor_discriminant q ε)
  rw [Real.sqrt_sq_eq_abs] at hh
  have hl := le_abs_self (1-q^2)
  unfold logFactor
  nlinarith [sq_nonneg ε]

lemma logFactor_pos (q ε : ℝ) : 0 < logFactor q ε := lt_of_lt_of_le zero_lt_one (logFactor_one_le q ε)

lemma logFactor_gt {q ε : ℝ} (hε : ε ≠ 0) : q < logFactor q ε := by
  have he := sq_pos_of_ne_zero hε
  have hs := Real.sqrt_nonneg ((1+q^2+ε^2)^2-4*q^2)
  unfold logFactor
  nlinarith [sq_nonneg (q-1)]

lemma logFactor_equation (q ε : ℝ) :
    logFactor q ε+q^2/logFactor q ε=1+q^2+ε^2 := by
  have hd : 0 ≤ (1+q^2+ε^2)^2-4*q^2 := (sq_nonneg _).trans (logFactor_discriminant q ε)
  have hs := Real.sq_sqrt hd
  have hl := (logFactor_pos q ε).ne'
  field_simp
  unfold logFactor
  nlinarith

lemma logFactor_norm_identity (q ε : ℝ) (z : Circle) :
    ‖1-(q:ℂ)*(z:ℂ)‖^2+ε^2 = logFactor q ε*‖1-(q/logFactor q ε:ℝ)*(z:ℂ)‖^2 := by
  have hz : (z:ℂ).re^2+(z:ℂ).im^2=1 := by
    have hh := Complex.sq_norm (z:ℂ)
    rw [z.norm_coe] at hh
    simp only [Complex.normSq_apply] at hh
    nlinarith
  have he := logFactor_equation q ε
  have hl := (logFactor_pos q ε).ne'
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,zero_sub,add_zero]
  field_simp at he ⊢
  nlinarith [congrArg (fun t => q^2*t) hz,congrArg (fun t => logFactor q ε*q^2*t) hz]

lemma logFactor_zero (q : ℝ) : logFactor q 0 = max 1 (q^2) := by
  have he : (1+q^2+(0:ℝ)^2)^2-4*q^2=(1-q^2)^2 := by ring
  unfold logFactor
  rw [he,Real.sqrt_sq_eq_abs]
  by_cases hq : q^2 ≤ 1
  · rw [abs_of_nonneg (by linarith),max_eq_left hq]; ring
  · rw [abs_of_nonpos (by linarith),max_eq_right (by linarith)]; ring

lemma logFactor_continuous : Continuous (fun p : ℝ × ℝ => logFactor p.1 p.2) := by
  unfold logFactor
  fun_prop

lemma circle_log_continuous {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun z : Circle => Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2)) := by
  apply Continuous.log
  · fun_prop
  · intro z
    apply pow_ne_zero
    apply norm_ne_zero_iff.mpr
    intro hz
    have hh := congrArg norm (sub_eq_zero.mp hz)
    rw [norm_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,z.norm_coe,mul_one] at hh
    linarith

lemma regularized_circle_moments {q ε : ℝ} (hq : 0 ≤ q) (hε : ε ≠ 0) (f : ℝ) :
    (∫ z : Circle, regularizedLog 1 ε ((q:ℂ)*(z:ℂ))*(1+f*(z:ℂ).re) ∂circleMeasure) =
      Real.log (logFactor q ε)-Real.log (1+ε^2)-f*q/logFactor q ε := by
  let r := q/logFactor q ε
  have hr : 0 ≤ r := div_nonneg hq (logFactor_pos q ε).le
  have hr1 : r < 1 := (div_lt_one (logFactor_pos q ε)).mpr (logFactor_gt hε)
  have hmom := circle_log_moments hr hr1
  have hi := compact_continuous_integrable (μ := circleMeasure) (circle_log_continuous hr hr1)
  have hic : Integrable (fun z : Circle => Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2)*(z:ℂ).re) circleMeasure := by
    apply compact_continuous_integrable
    exact (circle_log_continuous hr hr1).mul (by fun_prop)
  have he : ∀ z : Circle, regularizedLog 1 ε ((q:ℂ)*(z:ℂ)) =
      Real.log (logFactor q ε)-Real.log (1+ε^2)+Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2) := by
    intro z
    rw [regularizedLog_eq 1 ε _ hε]
    simp only [Complex.ofReal_one,one_mul]
    rw [logFactor_norm_identity,Real.log_mul (logFactor_pos q ε).ne' (by
      have hh := logFactor_norm_identity q ε z
      have hp : 0 < ‖1-(q:ℂ)*(z:ℂ)‖^2+ε^2 := by positivity
      exact ne_of_gt (pos_of_mul_pos_right (hh ▸ hp) (logFactor_pos q ε).le))]
    dsimp [r]
    ring
  let A := Real.log (logFactor q ε)-Real.log (1+ε^2)
  let g : Circle → ℝ := fun z => Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2)
  have hz : (∫ z : Circle, (z:ℂ).re ∂circleMeasure)=0 := by
    simpa [phaseChar] using circle_real_char_mean (by norm_num : (1:ℤ) ≠ 0)
  have he' : ∀ z : Circle, regularizedLog 1 ε ((q:ℂ)*(z:ℂ))*(1+f*(z:ℂ).re) =
      A+(A*f)*(z:ℂ).re+g z+f*(g z*(z:ℂ).re) := by
    intro z
    rw [he]
    dsimp [A,g]
    ring
  simp_rw [he']
  have hiz : Integrable (fun z : Circle => (z:ℂ).re) circleMeasure :=
    compact_continuous_integrable (by fun_prop)
  erw [integral_add (((integrable_const A).add (hiz.const_mul _)).add hi) (hic.const_mul _),
    integral_add ((integrable_const A).add (hiz.const_mul _)) hi,
    integral_add (integrable_const A) (hiz.const_mul _),integral_const_mul,integral_const_mul]
  change (∫ z : Circle, A ∂circleMeasure)+(A*f)*_+_+f*_=_
  rw [hmom.1,hmom.2,hz]
  simp [A,r]
  ring

end PinchedHartogs.BaseConstruction

end

end OAI
