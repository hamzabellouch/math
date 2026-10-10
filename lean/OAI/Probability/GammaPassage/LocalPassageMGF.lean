import OAI.Probability.GammaPassage.LocalExponentialEnergy
import OAI.Probability.GammaPassage.LocalIntegrability
import OAI.Probability.LatticePassage.EfronStein
import Mathlib.Probability.Moments.Basic

namespace OAI

namespace GammaFPP.FiniteLocal
open MeasureTheory ProbabilityTheory PlanarFPP Real
open scoped ENNReal

/-- Efron–Stein applied to `exp (a * F / 2)` gives a recursion for the local
passage-time moment-generating function. -/
theorem finitePassageTime_mgf_recursion {shape rate : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (a : ℝ) (ha : |a| ≤ rate/4) :
    mgf (finitePassageTime p q R) (finiteGammaMeasure shape rate) a ≤
      (mgf (finitePassageTime p q R) (finiteGammaMeasure shape rate) (a/2))^2 +
      ((16*(2 : ℝ)^shape/rate^2)*a^2*R) *
        mgf (finitePassageTime p q R) (finiteGammaMeasure shape rate) a := by
  classical
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  let P := finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate
  let : IsProbabilityMeasure P := by dsimp [P, finiteGammaMeasure]; infer_instance
  let F := finitePassageTime p q R
  let H := fun v => exp (a*F v/2)
  let B : ℝ := 16*(2 : ℝ)^shape/rate^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : Measurable F := measurable_finitePassageTime p q R hR
  have hHmeas : Measurable H := by dsimp [H]; fun_prop
  have hExp : Integrable (fun v => exp (a*F v)) P :=
    integrable_finitePassageTime_exp hs hr p q R hR a
      (by have hab := (le_abs_self a).trans ha; linarith)
  have hsq : (fun v => (H v)^2) = fun v => exp (a*F v) := by
    funext v
    dsimp [H]
    rw [pow_two, ← exp_add]
    congr 1
    ring
  have hH : MemLp H 2 P := by
    apply (memLp_two_iff_integrable_sq hHmeas.aestronglyMeasurable).mpr
    rw [hsq]
    exact hExp
  have henergy := finite_exponential_resampling_energy hs hr p q R hR a ha
  have hv : ENNReal.ofReal (variance H P) ≤
      ENNReal.ofReal ((B*a^2*R)*(∫ v, exp (a*F v) ∂P)) := by
    rw [variance_eq_integral hHmeas.aemeasurable,
      ofReal_integral_eq_lintegral_ofReal
        (f := fun v => (H v - ∫ w, H w ∂P)^2)
        (hH.sub (memLp_const _)).integrable_sq
        (by filter_upwards [] with v; positivity)]
    apply (CompanionFPP.centered_square_lintegral_le_resampling
      (gammaMeasure shape rate) hHmeas (hH.integrable (by norm_num))).trans
    apply henergy.trans_eq
    rw [← ofReal_integral_eq_lintegral_ofReal hExp
      (by filter_upwards [] with v; positivity)]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ B*a^2*R),
      ENNReal.ofReal_mul (by positivity : 0 ≤ B*a^2), ENNReal.ofReal_natCast]
  have hM : 0 ≤ ∫ v, exp (a*F v) ∂P := integral_nonneg (fun _ => (exp_pos _).le)
  have hv' := (ENNReal.ofReal_le_ofReal_iff
    (by positivity : 0 ≤ (B*a^2*R)*(∫ v, exp (a*F v) ∂P))).mp hv
  rw [variance_eq_sub hH] at hv'
  simp only [Pi.pow_apply] at hv'
  rw [hsq] at hv'
  have he : (∫ v, H v ∂P) = mgf F P (a/2) := by
    unfold mgf
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro v
    dsimp [H]
    congr 1
    ring
  rw [he] at hv'
  change mgf F P a ≤ (mgf F P (a/2))^2 + (B*a^2*R)*mgf F P a
  change mgf F P a - (mgf F P (a/2))^2 ≤ (B*a^2*R)*mgf F P a at hv'
  linarith

/-- The negative logarithm of `1 - x` is at most `2 * x` for `0 ≤ x ≤ 1 / 2`. -/
private lemma neg_log_one_sub_le (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/2) :
    -log (1-x) ≤ 2*x := by
  have hp : 0 < 1-x := by linarith
  have h := log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [log_inv] at h
  have hb : (1-x)⁻¹ - 1 ≤ 2*x := by
    rw [inv_eq_one_div]
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hp).mpr
    nlinarith
  exact h.trans hb

/-- Signed log-MGF recursion; the smallness condition is explicit. -/
theorem finitePassageTime_cgf_recursion {shape rate : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (a : ℝ) (ha : |a| ≤ rate/4)
    (hq : (16*(2 : ℝ)^shape/rate^2)*a^2*R ≤ 1/2) :
    cgf (finitePassageTime p q R) (finiteGammaMeasure shape rate) a ≤
      2*cgf (finitePassageTime p q R) (finiteGammaMeasure shape rate) (a/2) +
      2*((16*(2 : ℝ)^shape/rate^2)*a^2*R) := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  let P := finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate
  let : IsProbabilityMeasure P := by dsimp [P, finiteGammaMeasure]; infer_instance
  let F := finitePassageTime p q R
  let B : ℝ := 16*(2 : ℝ)^shape/rate^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hab := (le_abs_self a).trans ha
  have hM : 0 < mgf F P a := mgf_pos
    (integrable_finitePassageTime_exp hs hr p q R hR a (by linarith))
  have hM2 : 0 < mgf F P (a/2) := mgf_pos
    (integrable_finitePassageTime_exp hs hr p q R hR (a/2) (by linarith))
  have hrec := finitePassageTime_mgf_recursion hs hr p q R hR a ha
  have hden : 0 < 1-B*a^2*R := by change B*a^2*R ≤ 1/2 at hq; linarith
  have hbound : mgf F P a ≤ (mgf F P (a/2))^2/(1-B*a^2*R) := by
    apply (le_div_iff₀ hden).mpr
    change mgf F P a ≤ (mgf F P (a/2))^2 + (B*a^2*R)*mgf F P a at hrec
    nlinarith
  have hl := log_le_log hM hbound
  rw [log_div (pow_ne_zero _ hM2.ne') hden.ne', log_pow] at hl
  have hlog := neg_log_one_sub_le (B*a^2*R) (by positivity) hq
  change log (mgf F P a) ≤ 2*log (mgf F P (a/2)) + 2*(B*a^2*R)
  norm_num only [Nat.cast_ofNat] at hl
  linarith

end GammaFPP.FiniteLocal

end OAI
