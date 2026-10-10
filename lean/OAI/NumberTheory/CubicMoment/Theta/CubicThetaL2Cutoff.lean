import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialEnergyNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

namespace OAI

/-! Restriction to a measurable height region as a contraction on L2. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaL2CutoffFun (S : Set ℝ) (hS : MeasurableSet S) (F : CubicThetaRadialL2) :
    CubicThetaRadialL2 :=
  (Lp.memLp F |>.indicator hS).toLp (S.indicator F)

lemma cubicThetaL2CutoffFun_coe (S : Set ℝ) (hS : MeasurableSet S) (F : CubicThetaRadialL2) :
    cubicThetaL2CutoffFun S hS F =ᵐ[volume] S.indicator F :=
  MemLp.coeFn_toLp _

lemma cubicThetaL2CutoffFun_bound (S : Set ℝ) (hS : MeasurableSet S) (F : CubicThetaRadialL2) :
    ‖cubicThetaL2CutoffFun S hS F‖ ≤ ‖F‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cubicThetaL2CutoffFun_coe S hS F] with t ht
  rw [ht]
  exact norm_indicator_le_norm_self _ _

def cubicThetaL2CutoffLinear (S : Set ℝ) (hS : MeasurableSet S) :
    CubicThetaRadialL2 →ₗ[ℂ] CubicThetaRadialL2 where
  toFun := cubicThetaL2CutoffFun S hS
  map_add' F G := by
    apply Lp.ext
    filter_upwards [cubicThetaL2CutoffFun_coe S hS (F+G),
      cubicThetaL2CutoffFun_coe S hS F,cubicThetaL2CutoffFun_coe S hS G,
      Lp.coeFn_add F G,
      Lp.coeFn_add (cubicThetaL2CutoffFun S hS F) (cubicThetaL2CutoffFun S hS G)] with t hFG hF hG hsum hout
    simp only [Pi.add_apply] at hsum hout
    rw [hFG,hout,hF,hG]
    by_cases ht : t∈S
    · simp only [indicator_of_mem ht,hsum]
    · simp [indicator_of_notMem ht]
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [cubicThetaL2CutoffFun_coe S hS (c • F),
      cubicThetaL2CutoffFun_coe S hS F,Lp.coeFn_smul c F,
      Lp.coeFn_smul c (cubicThetaL2CutoffFun S hS F)] with t hCF hF hsmul hout
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply] at hsmul hout
    rw [hCF,hout,hF]
    by_cases ht : t∈S
    · simp only [indicator_of_mem ht,hsmul]
    · simp [indicator_of_notMem ht]

def cubicThetaL2Cutoff (S : Set ℝ) (hS : MeasurableSet S) :
    CubicThetaRadialL2 →L[ℂ] CubicThetaRadialL2 :=
  (cubicThetaL2CutoffLinear S hS).mkContinuous 1 (fun F => by
    change ‖cubicThetaL2CutoffFun S hS F‖ ≤ 1*‖F‖
    simpa only [one_mul] using cubicThetaL2CutoffFun_bound S hS F)

lemma cubicThetaL2Cutoff_coe (S : Set ℝ) (hS : MeasurableSet S) (F : CubicThetaRadialL2) :
    cubicThetaL2Cutoff S hS F =ᵐ[volume] S.indicator F := cubicThetaL2CutoffFun_coe S hS F

lemma cubicThetaL2Cutoff_norm_sq (S : Set ℝ) (hS : MeasurableSet S) (F : CubicThetaRadialL2) :
    ‖cubicThetaL2Cutoff S hS F‖^2=∫ t in S, ‖F t‖^2 := by
  rw [cubicTheta_l2_norm_sq,← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [cubicThetaL2Cutoff_coe S hS F] with t ht
  rw [ht]
  by_cases hmem : t∈S <;> simp [hmem]

end CubicFirstMoment

end

end OAI
