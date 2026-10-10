import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.WeightedAugment
import OAI.Probability.SKBarriers.Hierarchy.TimeChainOn
import OAI.Probability.SKBarriers.Hierarchy.ConstantWeightStats
import OAI.Probability.SKBarriers.Hierarchy.ConstantWeightMean
import OAI.Probability.SKBarriers.Hierarchy.WeightedListMean
import OAI.Probability.SKBarriers.Locking.NarrowRetainedStats

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

structure NarrowTimeBlocks (α : ℝ → ℝ) (r h q : ℝ) where
  before : TimeChainOn α 0 (r-h)
  left : TimeChainOn α (r-h) r
  right : TimeChainOn α r (r+h)
  after : TimeChainOn α (r+h) q
  tail : TimeChainOn α q 1

namespace NarrowTimeBlocks
variable {α : ℝ → ℝ} {r h q : ℝ} (B : NarrowTimeBlocks α r h q)

def common : TimeChainOn α 0 r := B.before.append B.left
def middle : TimeChainOn α r q := B.right.append B.after
def front : TimeChainOn α 0 q := B.common.append B.middle
def full : TimeChainOn α 0 1 := B.front.append B.tail

def b : List (ℝ × ℝ) := rawTimeChain B.before.chain
def l : List (ℝ × ℝ) := rawTimeChain B.left.chain
def j : List (ℝ × ℝ) := rawTimeChain B.right.chain
def k : List (ℝ × ℝ) := rawTimeChain B.after.chain
def t : List (ℝ × ℝ) := rawTimeChain B.tail.chain

def c (a : ℝ) : List (ℝ × (ℝ × ℝ)) := zeroWeightChain B.b++constantWeightChain (a/h) B.l
def v (θ : ℝ) : List (ℝ × (ℝ × ℝ)) := constantWeightChain (θ/h) B.j++zeroWeightChain B.k
def w (a : ℝ) : List (ℝ × (ℝ × ℝ)) := constantWeightChain (-a/h) B.j++zeroWeightChain B.k

@[simp] theorem c_underlying (a : ℝ) : weightedUnderlying (B.c a)=B.b++B.l := by
  simp only [c,weightedUnderlying_append,weightedUnderlying_zeroWeight,constantWeightChain_underlying]
@[simp] theorem v_underlying (θ : ℝ) : weightedUnderlying (B.v θ)=B.j++B.k := by
  simp only [v,weightedUnderlying_append,weightedUnderlying_zeroWeight,constantWeightChain_underlying]
@[simp] theorem w_underlying (a : ℝ) : weightedUnderlying (B.w a)=B.j++B.k := by
  simp only [w,weightedUnderlying_append,weightedUnderlying_zeroWeight,constantWeightChain_underlying]

theorem common_raw (a : ℝ) : rawTimeChain B.common.chain=weightedUnderlying (B.c a) := by
  simp only [common,TimeChainOn.append,rawTimeChain_append,c_underlying,b,l]
theorem middle_raw (a : ℝ) : rawTimeChain B.middle.chain=weightedUnderlying (B.w a) := by
  simp only [middle,TimeChainOn.append,rawTimeChain_append,w_underlying,j,k]
theorem front_raw (a : ℝ) : rawTimeChain B.front.chain=weightedUnderlying (B.c a)++weightedUnderlying (B.w a) := by
  rw [front,TimeChainOn.append,rawTimeChain_append,B.common_raw a,B.middle_raw a]
theorem full_raw (a : ℝ) : rawTimeChain B.full.chain=weightedUnderlying (B.c a)++weightedUnderlying (B.w a)++B.t := by
  rw [full,TimeChainOn.append,rawTimeChain_append,B.front_raw a]; rfl

@[simp] theorem l_variance : rawVariance B.l=h := by
  rw [l,rawVariance_rawTimeChain,B.left.duration]; ring
@[simp] theorem j_variance : rawVariance B.j=h := by
  rw [j,rawVariance_rawTimeChain,B.right.duration]; ring
@[simp] theorem common_variance (a : ℝ) : rawVariance (weightedUnderlying (B.c a))=r := by
  rw [← B.common_raw a,rawVariance_rawTimeChain,B.common.duration,sub_zero]
@[simp] theorem front_variance (a : ℝ) : rawVariance (weightedUnderlying (B.c a)++weightedUnderlying (B.w a))=q := by
  rw [← B.front_raw a,rawVariance_rawTimeChain,B.front.duration,sub_zero]
@[simp] theorem full_variance (a : ℝ) : rawVariance (weightedUnderlying (B.c a)++weightedUnderlying (B.w a)++B.t)=1 := by
  rw [← B.full_raw a,rawVariance_rawTimeChain,B.full.duration,sub_zero]

theorem cross_stats (hh : h≠0) (a θ : ℝ) :
    weightedCross (B.c a)=a ∧ weightedCross (B.v θ)=θ ∧ weightedCross (B.w a)=-a := by
  simp only [c,v,w,weightedCross_append,weightedCross_zeroWeight,constantWeightChain_cross,B.l_variance,B.j_variance,zero_add,add_zero]
  field_simp
  simp

theorem variance_stats (hh : h≠0) (a θ : ℝ) :
    narrowVariance (B.c a) (B.v θ) (B.w a)=(2*a^2+θ^2)/h := by
  simp only [narrowVariance,c,v,w,weightedVariance_append,weightedVariance_zeroWeight,constantWeightChain_variance,B.l_variance,B.j_variance,zero_add,add_zero]
  field_simp
  ring

theorem absCross_stats (hh : 0<h) {a θ : ℝ} (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    narrowAbsCross (B.c a) (B.v θ) (B.w a)=5*a+θ := by
  simp only [narrowAbsCross,c,v,w,weightedAbsCross_append,weightedAbsCross_zeroWeight,constantWeightChain_absCross,B.l_variance,B.j_variance,zero_add,add_zero]
  rw [abs_of_nonneg (div_nonneg ha hh.le),abs_of_nonneg (div_nonneg hθ hh.le),abs_div,abs_neg,abs_of_nonneg ha,abs_of_pos hh]
  field_simp
  ring

theorem v_mean (θ : ℝ) : weightedMean (B.v θ)=(θ/h)*rawArea B.j := by
  simp [v]

end NarrowTimeBlocks

end SK.Analytic

end
end

end OAI
