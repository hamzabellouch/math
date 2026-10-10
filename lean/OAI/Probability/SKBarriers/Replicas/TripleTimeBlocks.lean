import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.WeightedAugment
import OAI.Probability.SKBarriers.Hierarchy.TimeChainOn
import OAI.Probability.SKBarriers.Hierarchy.ConstantWeightStats

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

structure TripleTimeBlocks (α : ℝ → ℝ) (r s₁ s₂ q : ℝ) where
  common : TimeChainOn α 0 r
  before : TimeChainOn α r s₁
  active : TimeChainOn α s₁ s₂
  after : TimeChainOn α s₂ q
  tail : TimeChainOn α q 1

namespace TripleTimeBlocks
variable {α : ℝ → ℝ} {r s₁ s₂ q : ℝ} (B : TripleTimeBlocks α r s₁ s₂ q)

def front : TimeChainOn α 0 q := ((B.common.append B.before).append B.active).append B.after
def full : TimeChainOn α 0 1 := B.front.append B.tail
def early : TimeChainOn α 0 s₂ := (B.common.append B.before).append B.active

def c : List (ℝ × ℝ) := rawTimeChain B.common.chain
def b : List (ℝ × ℝ) := rawTimeChain B.before.chain
def a : List (ℝ × ℝ) := rawTimeChain B.active.chain
def d : List (ℝ × ℝ) := rawTimeChain B.after.chain
def t : List (ℝ × ℝ) := rawTimeChain B.tail.chain
def w (κ : ℝ) : List (ℝ × (ℝ × ℝ)) := zeroWeightChain B.b++constantWeightChain κ B.a++zeroWeightChain B.d

@[simp] theorem w_underlying (κ : ℝ) : weightedUnderlying (B.w κ)=B.b++B.a++B.d := by
  simp only [w,weightedUnderlying_append,weightedUnderlying_zeroWeight,constantWeightChain_underlying]

theorem prefix_raw (κ : ℝ) : rawTimeChain B.front.chain=B.c++weightedUnderlying (B.w κ) := by
  simp only [front,TimeChainOn.append,rawTimeChain_append,c,b,a,d,w_underlying,List.append_assoc]

theorem full_raw (κ : ℝ) : rawTimeChain B.full.chain=B.c++weightedUnderlying (B.w κ)++B.t := by
  rw [full,TimeChainOn.append,rawTimeChain_append,B.prefix_raw κ]; rfl

theorem early_raw : rawTimeChain B.early.chain=B.c++B.b++B.a := by
  simp only [early,TimeChainOn.append,rawTimeChain_append,c,b,a]

@[simp] theorem c_variance : rawVariance B.c=r := by rw [c,rawVariance_rawTimeChain,B.common.duration,sub_zero]
@[simp] theorem a_variance : rawVariance B.a=s₂-s₁ := by rw [a,rawVariance_rawTimeChain,B.active.duration]
@[simp] theorem prefix_variance (κ : ℝ) : rawVariance (B.c++weightedUnderlying (B.w κ))=q := by
  rw [← B.prefix_raw κ,rawVariance_rawTimeChain,B.front.duration,sub_zero]
@[simp] theorem full_variance (κ : ℝ) : rawVariance (B.c++weightedUnderlying (B.w κ)++B.t)=1 := by
  rw [← B.full_raw κ,rawVariance_rawTimeChain,B.full.duration,sub_zero]
@[simp] theorem early_variance : rawVariance (B.c++B.b++B.a)=s₂ := by
  rw [← B.early_raw,rawVariance_rawTimeChain,B.early.duration,sub_zero]

@[simp] theorem w_variance (κ : ℝ) : weightedVariance (B.w κ)=κ^2*(s₂-s₁) := by simp [w]
@[simp] theorem w_cross (κ : ℝ) : weightedCross (B.w κ)=κ*(s₂-s₁) := by simp [w]
@[simp] theorem w_absCross (κ : ℝ) : weightedAbsCross (B.w κ)=|κ| *(s₂-s₁) := by simp [w]

theorem w_penalty (κ : ℝ) : weightedCrossPenalty (B.w κ) 0=κ^2*rawPenalty B.a 0 := by
  simp [w,weightedCrossPenalty_append]

theorem normalized_stats (hs : s₁<s₂) :
    weightedVariance (B.w (s₂-s₁)⁻¹)=(s₂-s₁)⁻¹ ∧
    weightedCross (B.w (s₂-s₁)⁻¹)=1 ∧ weightedAbsCross (B.w (s₂-s₁)⁻¹)=1 := by
  have hpos : 0<s₂-s₁ := sub_pos.mpr hs
  rw [B.w_variance,B.w_cross,B.w_absCross,abs_of_pos (inv_pos.mpr hpos)]
  field_simp
  simp

theorem normalized_penalty (hm : Monotone α) (hs : s₁<s₂) :
    weightedCrossPenalty (B.w (s₂-s₁)⁻¹) 0∈Icc (α s₁) 1 := by
  have hpos : 0<s₂-s₁ := sub_pos.mpr hs
  have H := rawPenalty_bounds B.a (a:=α s₁) (b:=1) (q:=0)
    (fun p hp => ⟨B.active.raw_mass_lower hm p hp,(B.active.raw_mass p hp).2⟩) le_rfl
  simp only [B.a_variance,zero_add,zero_pow (by norm_num : 2≠0),sub_zero] at H
  rw [B.w_penalty]
  have H₁ := mul_le_mul_of_nonneg_left H.1 (sq_nonneg (s₂-s₁)⁻¹)
  have H₂ := mul_le_mul_of_nonneg_left H.2 (sq_nonneg (s₂-s₁)⁻¹)
  constructor
  · convert H₁ using 1
    field_simp
  · convert H₂ using 1
    field_simp

end TripleTimeBlocks

end SK.Analytic

end
end

end OAI
