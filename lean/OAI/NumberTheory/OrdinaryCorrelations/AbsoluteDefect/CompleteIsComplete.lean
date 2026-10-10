import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ModOneCharacter
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

namespace OrdinaryCorrelations.PretentiousEuler
open Set MeasureTheory Completion OrdinaryHorizontalHalasz OrdinaryLogDerivative
open OrdinaryHalaszEnvelopes OrdinaryPowerBounds OrdinaryDirichletMeanSquare

lemma complete_isComplete (f : ℕ → ℂ) : OrdinaryLogDerivative.Complete (complete f) :=
  fun m n _ _ => complete_mul f m n

lemma line_neg (δ t : ℝ) : line δ t = ((1+δ:ℝ):ℂ)+((-t:ℝ):ℂ)*Complex.I := by
  simp [line,sub_eq_add_neg]

theorem horizontal_envelope {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (T : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ B : ℝ, 0<B ∧ ∀u : ℝ, 0<u → ∀t : ℝ, |t|≤T →
      ‖LSeries (complete f) (line u t)‖ ≤ ε/u+B := by
  obtain ⟨η,hη,hη1,hηbound⟩ := compact_LSeries_saving hf hNP T hε
  refine ⟨1+1/η,by positivity,?_⟩
  intro u hu t ht
  by_cases huη : u≤η
  · have hh := hηbound u hu huη (-t) (by simpa using ht)
    rw [←line_neg] at hh
    exact hh.trans (le_add_of_nonneg_right (by positivity))
  · have hh := LSeries_norm_le (complete_oneBounded hf) (s:=line u t) (by simp; linarith)
    simp only [line_re,add_sub_cancel_left] at hh
    have hi : 1/u≤1/η := one_div_le_one_div_of_le hη (le_of_not_ge huη)
    have he : 0≤ε/u := by positivity
    linarith

lemma energyConstant_nonneg : 0≤energyConstant := by
  unfold energyConstant gaussianConstant
  positivity

lemma gaussian_integral_nonneg : 0≤∫ t : ℝ, gaussian t := integral_nonneg gaussian_nonneg

theorem actual_weighted_derivative_bound {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (T : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ B : ℝ, 0<B ∧ ∀δ : ℝ, 0<δ → δ≤1 →
      δ*(∫t in Icc (-T) T, gaussian t*‖deriv (LSeries (complete f)) (line δ t)‖) ≤
      10*energyConstant*ε +
        (2*Real.sqrt (∫t : ℝ, gaussian t)*Real.sqrt (5*energyConstant)+20*energyConstant*B)*Real.sqrt δ := by
  obtain ⟨B,hB,hbound⟩ := horizontal_envelope hf hNP T hε
  refine ⟨B,hB,?_⟩
  intro δ hδ hδ1
  have hu (x : ℝ) (hx : x∈Icc (0:ℝ) 1) : 0<δ+x := by linarith [hx.1]
  have hM : ContinuousOn (fun x => ε/(δ+x)+B) (Icc (0:ℝ) 1) :=
    (continuousOn_const.div (continuousOn_const.add continuousOn_id) (fun x hx => (hu x hx).ne')).add continuousOn_const
  have hM0 (x : ℝ) (hx : x∈Icc (0:ℝ) 1) : 0≤ε/(δ+x)+B := by
    exact add_nonneg (div_nonneg hε.le (hu x hx).le) hB.le
  have hpoint (x : ℝ) (hx : x∈Icc (0:ℝ) 1) (t : ℝ) (ht : t∈Icc (-T) T) :
      ‖LSeries (complete f) (line (δ+x) t)‖≤ε/(δ+x)+B :=
    hbound (δ+x) (hu x hx) t (abs_le.mpr ht)
  have hh := weighted_derivative_bound (complete_oneBounded hf) (complete_isComplete f)
    hδ (-T) T hM hM0 hpoint
  have he := envelope_integral energyConstant_nonneg hδ hδ1 hε.le hB.le
  have hh' := hh.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg (energyConstant*(2+1/δ)))))
  apply normalized_bound energyConstant_nonneg gaussian_integral_nonneg hδ hδ1 hε.le hB.le
  simpa only [mul_assoc] using hh'

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
