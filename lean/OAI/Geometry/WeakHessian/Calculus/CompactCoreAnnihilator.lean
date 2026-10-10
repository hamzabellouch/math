import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.CaccioppoliAlgebra
import OAI.Geometry.WeakHessian.Calculus.CompactCoreEquation
import OAI.Geometry.WeakHessian.LocalBounds.MetricPlateau

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile169
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.compact_core_caccioppoli {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (f : Lp ℝ 2 m)
    (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
    {η : X → ℝ} {L : ℝ≥0} (hη : LipschitzWith L η) (hηc : HasCompactSupport η)
    (hη1 : ∀ x,|η x| ≤ 1) :
    ‖boundedMulLp hη.continuous.aestronglyMeasurable (ae_of_all m hη1) f‖^2 ≤ (L:ℝ)^2*‖f‖^2 := by
  obtain ⟨χ,hχ,hχc,hχ1,-,⟨V,-,hηV,hV⟩,D,hD⟩ :=
    hrcd.exists_test_cutoff_in_open hN hfull hfin o hηc isOpen_univ (subset_univ _)
  have hc : ∀ x,η x ≠ 0 → χ x=1 := fun x hx => hV x (hηV (subset_tsupport η hx))
  let w := fun x => f x*χ x
  have hw : Sobolev m w := hrcd.compact_core_localized_sobolev hN hfull hfin o f hof hχ hχc hD
  have H := hrcd.compact_core_weak_equation hN hfull hfin o f hof hχ hχc hD hη hη1 hc
  have HG := integral_gamma_caccioppoli_lower hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2) hw hη hη1
  have hE : (∫ x,(w x*η x)^2 ∂m) ≤ (L:ℝ)^2*(∫ x,w x^2 ∂m) := by
    linarith only [H,HG]
  have hwf : (∫ x,w x^2 ∂m) ≤ ∫ x,(f x)^2 ∂m := by
    apply integral_mono_ae hw.1.integrable_sq (Lp.memLp f).integrable_sq
    exact ae_of_all _ fun x => by
      have hb : (χ x)^2 ≤ 1 := by nlinarith only [(hχ1 x).1,(hχ1 x).2]
      have HH := mul_le_mul_of_nonneg_left hb (sq_nonneg (f x))
      simpa only [w,mul_pow,mul_one] using HH
  let P := boundedMulLp hη.continuous.aestronglyMeasurable (ae_of_all m hη1)
  have hnorm : ‖P f‖^2 = ∫ x,(w x*η x)^2 ∂m := by
    have hn := norm_toLp_sq_eq_integral (Lp.memLp (P f))
    rw [Lp.toLp_coeFn] at hn
    apply hn.trans
    apply integral_congr_ae
    filter_upwards [boundedMulLp_ae _ (ae_of_all m hη1) f] with x hx
    change (P f) x = f x*η x at hx
    rw [hx]
    dsimp [w]
    by_cases he : η x=0
    · rw [he]; ring
    · rw [hc x he]; ring
  have hf : ‖f‖^2 = ∫ x,(f x)^2 ∂m := by
    simpa only [Lp.toLp_coeFn] using norm_toLp_sq_eq_integral (Lp.memLp f)
  rw [hnorm,hf]
  exact hE.trans (mul_le_mul_of_nonneg_left hwf (sq_nonneg _))

lemma RCD.compact_core_annihilator_zero {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (f : Lp ℝ 2 m)
    (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0) : f = 0 := by
  have hb (n : ℕ) (x : X) : |radialCutoff o n x| ≤ 1 := by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]
    exact radialCutoff_le_one o n x
  let P (n : ℕ) := boundedMulLp (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable (ae_of_all m (hb n))
  have hT : Tendsto (fun n => P n f) atTop (𝓝 f) :=
    boundedMulLp_tendsto (fun n => (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable)
      (fun n => ae_of_all m (hb n)) (ae_of_all m (radialCutoff_tendsto o)) f
  have he (n : ℕ) : ‖P n f‖^2 ≤ (1/((n:ℝ)+1))^2*‖f‖^2 := by
    simpa only [NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,one_div] using
      hrcd.compact_core_caccioppoli hN hfull hfin o f hof (radialCutoff_lipschitz o n) (radialCutoff_compact o n) (hb n)
  have hl : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))^2*‖f‖^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2 |>.mul_const (‖f‖^2)
  have hh : ‖f‖^2 ≤ 0 := le_of_tendsto_of_tendsto (hT.norm.pow 2) hl (Eventually.of_forall he)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hh (sq_nonneg _)))
end WeakHessian

end
end InlinedFile169

end OAI
