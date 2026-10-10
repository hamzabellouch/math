import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Line
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ContinuousOnShiftRpow

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set

namespace OrdinaryHorizontalHalasz
open MeasureTheory Set OrdinaryLogDerivative OrdinaryDirichletMeanSquare
open OrdinaryPowerBounds OrdinaryHalaszEnvelopes

def derivativeConstant : ℝ :=
  30*energyConstant+2*Real.sqrt (∫ t : ℝ, gaussian t)*Real.sqrt (5*energyConstant)

lemma energyConstant_nonneg : 0≤energyConstant := by
  unfold energyConstant gaussianConstant
  positivity

lemma derivativeConstant_nonneg : 0≤derivativeConstant := by
  have hC := energyConstant_nonneg
  unfold derivativeConstant
  positivity

theorem uniform_derivative_bound {f : ℕ → ℂ} (hf : ∀n, ‖f n‖≤1)
    (hm : Complete f) {δ : ℝ} (hδ : 0<δ) (hδ1 : δ≤1) (l r : ℝ) :
    δ*(∫t in Icc l r, gaussian t*‖deriv (LSeries f) (line δ t)‖) ≤ derivativeConstant := by
  have hu (x : ℝ) (hx : x∈Icc (0:ℝ) 1) : 0<δ+x := by linarith [hx.1]
  have hM : ContinuousOn (fun x : ℝ => 1/(δ+x)+1) (Icc 0 1) :=
    (continuousOn_const.div (continuousOn_const.add continuousOn_id) (fun x hx => (hu x hx).ne')).add continuousOn_const
  have hM0 (x : ℝ) (hx : x∈Icc (0:ℝ) 1) : 0≤1/(δ+x)+1 := by
    exact add_nonneg (div_nonneg zero_le_one (hu x hx).le) zero_le_one
  have hb (x : ℝ) (hx : x∈Icc (0:ℝ) 1) (t : ℝ) (_ht : t∈Icc l r) :
      ‖LSeries f (line (δ+x) t)‖≤1/(δ+x)+1 := by
    have hh := LSeries_norm_le hf (s:=line (δ+x) t) (by simp; linarith [hu x hx])
    have he : 1+(δ+x)-1=δ+x := by ring
    rw [line_re,he] at hh
    linarith
  have hh := weighted_derivative_bound hf hm hδ l r hM hM0 hb
  have he := envelope_integral energyConstant_nonneg hδ hδ1 (show (0:ℝ)≤1 by norm_num) (show (0:ℝ)≤1 by norm_num)
  have hh' := hh.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg (energyConstant*(2+1/δ)))))
  have hn := normalized_bound energyConstant_nonneg
    (integral_nonneg gaussian_nonneg) hδ hδ1 (show (0:ℝ)≤1 by norm_num) (show (0:ℝ)≤1 by norm_num)
    (by simpa only [mul_assoc] using hh')
  have hs : Real.sqrt δ≤1 := by simpa using Real.sqrt_le_sqrt hδ1
  have hc : 0≤2*Real.sqrt (∫ t : ℝ, gaussian t)*Real.sqrt (5*energyConstant)+20*energyConstant*1 := by
    have hC := energyConstant_nonneg
    positivity
  exact hn.trans (by unfold derivativeConstant; nlinarith [mul_le_mul_of_nonneg_left hs hc])

lemma derivative_gaussian_integrable {f : ℕ → ℂ} (hf : ∀n, ‖f n‖≤1)
    {δ : ℝ} (hδ : 0<δ) :
    Integrable (fun t : ℝ => gaussian t*‖deriv (LSeries f) (line δ t)‖) := by
  have hconv : LSeries.abscissaOfAbsConv f ≤ (1:ℝ) := LSeries.abscissaOfAbsConv_le_of_le_const ⟨1,fun n _ => hf n⟩
  have hlog : Summable (fun n => ‖LSeries.term (LSeries.logMul f) (line δ 0) n‖) := by
    exact (LSeriesSummable_logMul_of_lt_re (lt_of_le_of_lt hconv
      (by exact_mod_cast (show 1<(line δ 0).re by simp; linarith)))).norm
  have hmm : ∀ t, ‖deriv (LSeries f) (line δ t)‖≤∑'n, ‖LSeries.term (LSeries.logMul f) (line δ 0) n‖ := by
    intro t
    rw [LSeries_deriv (lt_of_le_of_lt hconv (by exact_mod_cast (show 1<(line δ t).re by simp; linarith))),norm_neg]
    have he : ∀ n, ‖LSeries.term (LSeries.logMul f) (line δ t) n‖=
        ‖LSeries.term (LSeries.logMul f) (line δ 0) n‖ := by
      intro n
      rw [LSeries.norm_term_eq,LSeries.norm_term_eq]
      simp
    exact (norm_tsum_le_tsum_norm (hlog.congr (fun n => (he n).symm))).trans_eq (tsum_congr he)
  have hc : Continuous (fun t : ℝ => deriv (LSeries f) (line δ t)) := by
    have he : (fun t : ℝ => deriv (LSeries f) (line δ t)) =
        fun t => -LSeries (LSeries.logMul f) (line δ t) := by
      funext t
      exact LSeries_deriv (lt_of_le_of_lt hconv (by exact_mod_cast (show 1<(line δ t).re by simp; linarith)))
    rw [he]
    exact (continuous_vertical (by simpa only [LSeries.abscissaOfAbsConv_logMul] using hconv) hδ).neg
  apply Integrable.mono' (gaussian_integrable.mul_const (∑'n, ‖LSeries.term (LSeries.logMul f) (line δ 0) n‖))
  · exact ((by unfold gaussian; fun_prop : Continuous gaussian).mul hc.norm).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (gaussian_nonneg _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hmm t) (gaussian_nonneg _))

theorem uniform_derivative_global {f : ℕ → ℂ} (hf : ∀n, ‖f n‖≤1)
    (hm : Complete f) {δ : ℝ} (hδ : 0<δ) (hδ1 : δ≤1) :
    δ*(∫t : ℝ, gaussian t*‖deriv (LSeries f) (line δ t)‖) ≤ derivativeConstant := by
  have hi := derivative_gaussian_integrable hf hδ
  have hh := (aecover_Icc («μ» := volume) (Filter.tendsto_neg_atTop_atBot :
    Filter.Tendsto (fun t : ℝ => -t) Filter.atTop Filter.atBot)
    (Filter.tendsto_id : Filter.Tendsto (fun t : ℝ => t) Filter.atTop Filter.atTop)).integral_tendsto_of_countably_generated hi
  exact le_of_tendsto (hh.const_mul δ)
    (Filter.Eventually.of_forall (fun t => uniform_derivative_bound hf hm hδ hδ1 (-t) t))

end OrdinaryHorizontalHalasz

end

end OAI
