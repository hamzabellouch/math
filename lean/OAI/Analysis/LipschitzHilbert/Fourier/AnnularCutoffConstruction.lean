import OAI.Analysis.LipschitzHilbert.Fourier.ReflectedBandProjection
import Mathlib.Analysis.Calculus.BumpFunction.Normed

namespace OAI

/-! Explicit real annular cutoffs and the low-pass difference underlying
the geometric frequency partition. All supports stay inside fixed bands. -/
noncomputable section
open MeasureTheory Function Set
namespace LipschitzHilbert.PacketRepresentation

def reassemblyLowBump : ContDiffBump (0:ℝ) where
  rIn := 1
  rOut := 13/12
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def reassemblyLow : SchwartzMap ℝ ℂ :=
  (reassemblyLowBump.hasCompactSupport.toSchwartzMap reassemblyLowBump.contDiff).postcompCLM Complex.ofRealCLM

@[simp] theorem reassemblyLow_apply (s : ℝ) : reassemblyLow s=(reassemblyLowBump s : ℂ) := rfl

def reassemblyOuterBump : ContDiffBump (3/2:ℝ) where
  rIn := 3/8
  rOut := 1/2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def reassemblyOuter : SchwartzMap ℝ ℂ :=
  (reassemblyOuterBump.hasCompactSupport.toSchwartzMap reassemblyOuterBump.contDiff).postcompCLM Complex.ofRealCLM

@[simp] theorem reassemblyOuter_apply (s : ℝ) : reassemblyOuter s=(reassemblyOuterBump s : ℂ) := rfl

theorem reassemblyOuter_support (s : ℝ) (hs : reassemblyOuter s≠0) : 1≤s ∧ s≤2 := by
  have hn : reassemblyOuterBump s≠0 := by
    intro hz
    exact hs (by simp only [reassemblyOuter_apply,hz,Complex.ofReal_zero])
  have hd : |s-3/2|<1/2 := by
    have hmem : s∈support reassemblyOuterBump := hn
    rw [reassemblyOuterBump.support_eq] at hmem
    simpa only [Metric.mem_ball,Real.dist_eq,reassemblyOuterBump] using hmem
  exact ⟨by linarith [(abs_lt.mp hd).1],by linarith [(abs_lt.mp hd).2]⟩

theorem reassemblyOuter_one (s : ℝ) (hs : 9/8≤s ∧ s≤15/8) : reassemblyOuter s=1 := by
  have hd : s∈Metric.closedBall (3/2:ℝ) reassemblyOuterBump.rIn := by
    simp only [Metric.mem_closedBall,Real.dist_eq,reassemblyOuterBump]
    exact abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
  simp only [reassemblyOuter_apply,reassemblyOuterBump.one_of_mem_closedBall hd,Complex.ofReal_one]

theorem reassemblyLow_one (s : ℝ) (hs : |s|≤1) : reassemblyLow s=1 := by
  have hd : s∈Metric.closedBall (0:ℝ) reassemblyLowBump.rIn := by
    simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,reassemblyLowBump] using hs
  simp only [reassemblyLow_apply,reassemblyLowBump.one_of_mem_closedBall hd,Complex.ofReal_one]

theorem reassemblyLow_zero (s : ℝ) (hs : 13/12≤|s|) : reassemblyLow s=0 := by
  have hd : reassemblyLowBump.rOut≤dist s 0 := by
    simpa only [Real.dist_eq,sub_zero,reassemblyLowBump] using hs
  simp only [reassemblyLow_apply,reassemblyLowBump.zero_of_le_dist hd,Complex.ofReal_zero]

def reassemblyDifference (s : ℝ) : ℂ := reassemblyLow ((16/27)*s)-reassemblyLow ((8/9)*s)

theorem reassemblyDifference_small (s : ℝ) (hs : |s|≤9/8) : reassemblyDifference s=0 := by
  have h1 : |(16/27)*s|≤1 := by rw [abs_mul]; norm_num; linarith only [hs]
  have h2 : |(8/9)*s|≤1 := by rw [abs_mul]; norm_num; linarith only [hs]
  simp only [reassemblyDifference,reassemblyLow_one _ h1,reassemblyLow_one _ h2,sub_self]

theorem reassemblyDifference_large (s : ℝ) (hs : 117/64≤|s|) : reassemblyDifference s=0 := by
  have h1 : 13/12≤|(16/27)*s| := by rw [abs_mul]; norm_num; linarith only [hs]
  have h2 : 13/12≤|(8/9)*s| := by rw [abs_mul]; norm_num; linarith only [hs]
  simp only [reassemblyDifference,reassemblyLow_zero _ h1,reassemblyLow_zero _ h2,sub_self]

end LipschitzHilbert.PacketRepresentation

end

end OAI
