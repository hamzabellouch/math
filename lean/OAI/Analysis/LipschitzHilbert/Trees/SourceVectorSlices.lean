import OAI.Analysis.LipschitzHilbert.Fourier.PlanarSchwartzSlice
import OAI.Analysis.LipschitzHilbert.Trees.SourceVectorReproduction

namespace OAI

/-! Actual coordinate restrictions of Hilbert-valued planar Schwartz
packets, needed to reproduce non-tensor packet sums. -/
noncomputable section
open scoped NNReal
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

def vectorHorizontalSlice (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (y : ℝ) : SchwartzMap ℝ (EuclideanSpace ℂ κ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun x : ℝ => (x,y+0*x))
    (affineLine_temperate y 0) (affineLine_antilipschitz y 0) f

@[simp] theorem vectorHorizontalSlice_apply
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (y x : ℝ) :
    vectorHorizontalSlice f y x=f (x,y) := by
  change f (x,y+0*x)=f (x,y)
  simp only [zero_mul,add_zero]

theorem verticalLine_temperate (x : ℝ) :
    Function.HasTemperateGrowth (fun y : ℝ => (x,y)) := by
  let A : ℝ →L[ℝ] (ℝ×ℝ) := (0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)
  have h := (Function.HasTemperateGrowth.const (E:=ℝ) (x,0)).add A.hasTemperateGrowth
  change Function.HasTemperateGrowth (fun y => (x,0)+A y) at h
  simpa only [A,ContinuousLinearMap.prod_apply,zero_apply,
    ContinuousLinearMap.id_apply,Prod.mk_add_mk,add_zero,zero_add] using h

theorem verticalLine_antilipschitz (x : ℝ) :
    AntilipschitzWith 1 (fun y : ℝ => (x,y)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro y z
  simp only [NNReal.coe_one,one_mul,Prod.dist_eq]
  exact le_max_right _ _

def vectorVerticalSlice (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (x : ℝ) : SchwartzMap ℝ (EuclideanSpace ℂ κ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun y : ℝ => (x,y))
    (verticalLine_temperate x) (verticalLine_antilipschitz x) f

@[simp] theorem vectorVerticalSlice_apply
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (x y : ℝ) :
    vectorVerticalSlice f x y=f (x,y) := rfl

end LipschitzHilbert

end

end OAI
