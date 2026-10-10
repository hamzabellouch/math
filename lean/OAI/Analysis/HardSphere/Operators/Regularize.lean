import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HilbertRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def regularize (ε : ℝ) (z : E) : ℂ := (Real.sqrt (‖z‖^2+ε^2)-ε : ℝ)

def differential (ε : ℝ) (z : E) : E →L[ℝ] ℂ :=
  (Real.sqrt (‖z‖^2+ε^2))⁻¹ • (Complex.ofRealCLM.comp (innerSL ℝ z))

lemma smooth {ε : ℝ} (hε : 0<ε) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (regularize (E := E) ε) := by
  apply Complex.ofRealCLM.contDiff.comp
  apply ContDiff.sub _ contDiff_const
  apply ContDiff.sqrt ((contDiff_norm_sq ℝ).add contDiff_const)
  intro z
  positivity

omit [InnerProductSpace ℝ E] in
lemma zero {ε : ℝ} (hε : 0≤ε) : regularize (E := E) ε 0=0 := by
  simp [regularize,Real.sqrt_sq hε]

lemma hasFDerivAt {ε : ℝ} (hε : 0<ε) (z : E) :
    HasFDerivAt (regularize ε) (differential ε z) z := by
  have hn : ‖z‖^2+ε^2≠0 := by positivity
  have h := Complex.ofRealCLM.hasFDerivAt.comp z
    ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε^2)).sqrt hn).sub_const ε)
  have hd : differential ε z = Complex.ofRealCLM.comp
      ((1/(2*Real.sqrt (‖z‖^2+ε^2))) • (2 • innerSL ℝ z)) := by
    ext w
    simp [differential,two_smul,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hd]
  exact h

omit [InnerProductSpace ℝ E] in
lemma sqroot_ge_norm (ε : ℝ) (z : E) : ‖z‖≤Real.sqrt (‖z‖^2+ε^2) :=
  (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by nlinarith [sq_nonneg ε])

lemma differential_apply_le (ε : ℝ) (z w : E) : ‖differential ε z w‖≤‖w‖ := by
  by_cases hz : z=0
  · simp [hz,differential]
  have hp : 0<Real.sqrt (‖z‖^2+ε^2) :=
    lt_of_lt_of_le (norm_pos_iff.mpr hz) (sqroot_ge_norm ε z)
  simp only [differential,smul_apply,ContinuousLinearMap.comp_apply,norm_smul,
    Complex.ofRealCLM_apply,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_pos hp,innerSL_apply_apply]
  change _*‖inner ℝ z w‖≤_
  apply le_trans (mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℝ) z w) (by positivity :
    0≤(Real.sqrt (‖z‖^2+ε^2))⁻¹))
  rw [← div_eq_inv_mul,div_le_iff₀ hp]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (sqroot_ge_norm ε z) (norm_nonneg w)

lemma differential_le (ε : ℝ) (z : E) : ‖differential ε z‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  simpa only [one_mul] using differential_apply_le ε z w

lemma fderiv_eq {ε : ℝ} (hε : 0<ε) (z : E) :
    fderiv ℝ (regularize ε) z=differential ε z := (hasFDerivAt hε z).fderiv

lemma lipschitz {ε : ℝ} (hε : 0<ε) : LipschitzWith 1 (regularize (E := E) ε) :=
  lipschitzWith_of_nnnorm_fderiv_le ((smooth hε).differentiable (by simp))
    (fun z ↦ by rw [fderiv_eq hε]; exact NNReal.coe_le_coe.mp (differential_le ε z))

lemma norm_le {ε : ℝ} (hε : 0<ε) (z : E) : ‖regularize ε z‖≤‖z‖ := by
  simpa only [zero hε.le,sub_zero,NNReal.coe_one,one_mul] using
    (lipschitz hε).norm_sub_le z 0

omit [InnerProductSpace ℝ E] in
lemma tendsto_regularize (z : E) {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n ↦ regularize (e n) z) atTop (𝓝 (‖z‖ : ℂ)) := by
  have h : Tendsto (fun n ↦ Real.sqrt (‖z‖^2+e n^2)-e n) atTop (𝓝 ‖z‖) := by
    have h := (((tendsto_const_nhds (x := ‖z‖^2)).add (he.pow 2)).sqrt.sub he)
    simpa only [zero_pow (by norm_num : 2≠0),add_zero,sub_zero,Real.sqrt_sq (norm_nonneg _)] using h
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp h

end HilbertRegularization

end

end OAI
