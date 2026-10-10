import OAI.NumberTheory.CubicMoment.Estimates.MellinWeightFamily

namespace OAI

/-! Reindexing and finite-coordinate assembly for uniform smooth weights. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

 def UniformLogWeights.reindex {α β : Type*} {W : α → ℝ → ℂ}
    (h : UniformLogWeights W) (f : β → α) : UniformLogWeights (fun b => W (f b)) where
  compact b := h.compact (f b)
  positive b := h.positive (f b)
  smooth b := h.smooth (f b)
  radius := h.radius
  radius_nonneg := h.radius_nonneg
  support_bound b u hu := h.support_bound (f b) u hu
  derivative_bound n := by
    obtain ⟨B,hB,hbound⟩ := h.derivative_bound n
    exact ⟨B,hB,fun b u => hbound (f b) u⟩

 def UniformLogWeights.finiteCoordinates {γ ι : Type*} [Fintype ι]
    (W : γ → ι → ℝ → ℂ) (h : ∀ i, UniformLogWeights (fun u => W u i)) :
    UniformLogWeights (fun z : γ × ι => W z.1 z.2) where
  compact z := (h z.2).compact z.1
  positive z := (h z.2).positive z.1
  smooth z := (h z.2).smooth z.1
  radius := ∑ i, (h i).radius
  radius_nonneg := Finset.sum_nonneg (fun i _ => (h i).radius_nonneg)
  support_bound z u hu := ((h z.2).support_bound z.1 u hu).trans
    (Finset.single_le_sum (fun i _ => (h i).radius_nonneg) (Finset.mem_univ z.2))
  derivative_bound n := by
    choose B hB hbound using fun i => (h i).derivative_bound n
    refine ⟨∑ i, B i,Finset.sum_nonneg (fun i _ => hB i),?_⟩
    intro z u
    exact (hbound z.2 z.1 u).trans
      (Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ z.2))

end CubicFirstMoment

end

end OAI
