import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneOrZero
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CompleteIsComplete

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
open Set MeasureTheory OrdinaryHorizontalHalasz OrdinaryDirichletMeanSquare

theorem compact_derivative_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (T : ℝ) {ζ : ℝ} (hζ : 0<ζ) :
    ∃ η : ℝ, 0<η ∧ ∀ δ : ℝ, 0<δ → δ≤η →
      δ*(∫t in Icc (-T) T, gaussian t*‖deriv (LSeries (Completion.complete f)) (line δ t)‖) ≤ ζ := by
  let C := energyConstant
  have hC : 0≤C := energyConstant_nonneg
  let ε := ζ/(20*(C+1))
  have hε : 0<ε := by dsimp [ε]; positivity
  obtain ⟨B,hB,hbound⟩ := actual_weighted_derivative_bound hf hNP T hε
  let K := 2*Real.sqrt (∫t : ℝ, gaussian t)*Real.sqrt (5*C)+20*C*B
  have hK : 0≤K := by dsimp [K]; positivity
  let r := ζ/(2*(K+1))
  have hr : 0<r := by dsimp [r]; positivity
  refine ⟨min 1 (r^2), lt_min (by norm_num) (sq_pos_of_pos hr), ?_⟩
  intro δ hδ hδη
  have hd1 := hδη.trans (min_le_left _ _)
  have hdr : Real.sqrt δ≤r := (Real.sqrt_le_left hr.le).2 (hδη.trans (min_le_right _ _))
  have he : 10*C*ε ≤ ζ/2 := by
    dsimp [ε]
    have hx := (div_mul_cancel₀ ζ (ne_of_gt (show 0<20*(C+1) by positivity)))
    nlinarith [hε.le]
  have hk : K*r ≤ ζ/2 := by
    have hx := (div_mul_cancel₀ ζ (ne_of_gt (show 0<2*(K+1) by positivity)))
    change r*(2*(K+1))=ζ at hx
    nlinarith [hr.le]
  have hh := hbound δ hδ hd1
  change δ*(∫t in Icc (-T) T, gaussian t*‖deriv (LSeries (Completion.complete f)) (line δ t)‖) ≤
    10*C*ε+K*Real.sqrt δ at hh
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hdr hK])

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
