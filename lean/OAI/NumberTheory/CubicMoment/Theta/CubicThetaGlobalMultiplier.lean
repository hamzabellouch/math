import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

namespace OAI

/-! Bounded multiplication on the actual quotient L2 space. This is used
to reconstruct core cutoffs from the compact coordinate inclusions. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

variable {φ : CubicThetaQuotient → ℂ} (hφ : AEStronglyMeasurable φ cubicThetaQuotientMeasure)
  {C : ℝ} (hbound : ∀ q, ‖φ q‖≤C)

include hφ hbound in
private lemma multiplier_memLp (u : CubicThetaGlobalL2) :
    MemLp (fun q => φ q*u q) 2 cubicThetaQuotientMeasure := by
  apply (Lp.memLp u).of_le_mul (c:=C) (hφ.mul (Lp.aestronglyMeasurable u))
  filter_upwards with q
  change ‖φ q*u q‖≤C*‖u q‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound q) (_root_.norm_nonneg _)

def cubicThetaGlobalMultiplierLinear : CubicThetaGlobalL2 →ₗ[ℂ] CubicThetaGlobalL2 where
  toFun u := (multiplier_memLp hφ hbound u).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(multiplier_memLp hφ hbound (u+v)).coeFn_toLp,
      (multiplier_memLp hφ hbound u).coeFn_toLp,(multiplier_memLp hφ hbound v).coeFn_toLp,
      Lp.coeFn_add u v,
      Lp.coeFn_add ((multiplier_memLp hφ hbound u).toLp _)
        ((multiplier_memLp hφ hbound v).toLp _)] with q hsum hu hv huv hadd
    simp only [Pi.add_apply] at huv hadd
    rw [hsum,hadd,hu,hv,huv]
    ring
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(multiplier_memLp hφ hbound (c • u)).coeFn_toLp,
      (multiplier_memLp hφ hbound u).coeFn_toLp,Lp.coeFn_smul c u,
      Lp.coeFn_smul c ((multiplier_memLp hφ hbound u).toLp _)] with q hmul hu hcu hadd
    simp only [Pi.smul_apply,RingHom.id_apply] at hcu hadd ⊢
    rw [hmul,hadd,hu,hcu]
    simp only [smul_eq_mul]
    ring

lemma cubicThetaGlobalMultiplierLinear_bound (u : CubicThetaGlobalL2) :
    ‖cubicThetaGlobalMultiplierLinear hφ hbound u‖≤C*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(multiplier_memLp hφ hbound u).coeFn_toLp] with q hq
  change ‖((multiplier_memLp hφ hbound u).toLp _) q‖≤C*‖u q‖
  rw [hq,norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound q) (_root_.norm_nonneg _)

def cubicThetaGlobalMultiplier : CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 :=
  (cubicThetaGlobalMultiplierLinear hφ hbound).mkContinuous C
    (cubicThetaGlobalMultiplierLinear_bound hφ hbound)

lemma cubicThetaGlobalMultiplier_ae (u : CubicThetaGlobalL2) :
    (cubicThetaGlobalMultiplier hφ hbound u : CubicThetaQuotient → ℂ)=ᵐ[cubicThetaQuotientMeasure]
      fun q => φ q*u q := (multiplier_memLp hφ hbound u).coeFn_toLp

end CubicFirstMoment

end

end OAI
