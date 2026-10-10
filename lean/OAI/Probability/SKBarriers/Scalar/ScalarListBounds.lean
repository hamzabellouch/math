import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarHierarchyAverageAlgebra
import OAI.Probability.SKBarriers.Scalar.ScalarSpatialAverage
import OAI.Probability.SKBarriers.Scalar.ScalarWeightedVector
import OAI.Probability.SKBarriers.Replicas.TripleRetainedStats

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem scalarIncrementChain_lipschitz (l : List (ℝ × ℝ))
    (hm : ∀ p∈l,0≤p.1) {f : ℝ → ℝ} (hf : BoundedDerivs f) {K : ℝ≥0} (hL : LipschitzWith K f) :
    LipschitzWith K (scalarIncrementChain l f) := by
  rw [scalarIncrementChain_get]
  exact scalarHierarchy_lipschitz _ _ _ (fun i => hm _ (List.get_mem l i)) hf hL

theorem scalarIncrementChain_spin_convex (l : List (ℝ × ℝ))
    (hm : ∀ p∈l,p.1∈Icc (0:ℝ) 1) : ScalarSpinConvex (scalarIncrementChain l scalarSpinTerminal) := by
  rw [scalarIncrementChain_get]
  intro x
  have H := (scalarHierarchy_spin_derivative_bounds l.length (fun i => (l.get i).1)
    (fun i => (l.get i).2) (fun i => hm _ (List.get_mem l i)) x).2
  exact ⟨H.1.le,H.2⟩

theorem scalarIncrementChain_hessian_lipschitz (l : List (ℝ × ℝ))
    (hm : ∀ p∈l,p.1∈Icc (0:ℝ) 1) (hs : l.Pairwise (fun p q => p.1≤q.1)) :
    LipschitzWith susceptibilityLipschitzConstant (rootHessian 0 (scalarIncrementChain l scalarSpinTerminal)) := by
  rw [scalarIncrementChain_get]
  exact scalarHierarchy_spin_hessian_lipschitz _ _ _ (fun i => hm _ (List.get_mem l i)) (mass_get_monotone hs)

theorem scalarIncrementAverage_bounded (l : List (ℝ × ℝ)) {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedScalar g) : BoundedScalar (scalarIncrementAverage l f g) := by
  rw [scalarIncrementAverage_get]
  exact scalarHierarchyAverage_bounded hf hg _ _ _

theorem scalarIncrementAverage_abs_le (l : List (ℝ × ℝ)) {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) {C : ℝ} (hg : ∀ x,|g x|≤C) (x : ℝ) :
    |scalarIncrementAverage l f g x|≤C := by
  rw [scalarIncrementAverage_get]
  exact scalarHierarchyAverage_abs_le hf hg _ _ _ _

theorem scalarIncrementAverage_nonneg (l : List (ℝ × ℝ)) {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedScalar g) (hpos : ∀ x,0≤g x) (x : ℝ) :
    0 ≤ scalarIncrementAverage l f g x := by
  rw [scalarIncrementAverage_get,scalarHierarchyAverage_integral hf hg]
  exact integral_nonneg (fun _ => hpos _)

theorem weightedAverage_nonneg (w : List (ℝ × (ℝ × ℝ))) {f : ℝ → ℝ}
    (hf : BoundedDerivs f) (x : ℝ) :
    0≤vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (x,0) := by
  rw [vectorIncrementAverage_get]
  have h : (fun i : Fin w.length => ((w.get i).2.1,(w.get i).2.2))=fun i => (w.get i).2 := rfl
  simpa only [scalarWeightedAverage,h] using
    scalarWeightedAverage_nonneg w.length (fun i => (w.get i).1) (fun i => (w.get i).2.1)
      (fun i => (w.get i).2.2) hf x

def weightedMomentBound (w : List (ℝ × (ℝ × ℝ))) : ℝ := 2*weightedVariance w+(2*weightedAbsCross w)^2

theorem weightedMomentBound_nonneg (w : List (ℝ × (ℝ × ℝ))) : 0≤weightedMomentBound w := by
  have H : 0≤weightedVariance w := List.sum_nonneg (by intro a ha; obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha; exact sq_nonneg _)
  dsimp [weightedMomentBound]; positivity

theorem weightedAverage_abs_le (w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈w,p.1∈Icc (0:ℝ) 1) (hs : w.Pairwise (fun p q => p.1≤q.1))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hL : LipschitzWith 1 f) (x : ℝ) :
    |vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (x,0)|≤weightedMomentBound w := by
  rw [abs_of_nonneg (weightedAverage_nonneg w hf x),vectorIncrementAverage_get]
  have H := scalarWeightedAverage_le w.length (fun i => (w.get i).1) (fun i => (w.get i).2.1)
    (fun i => (w.get i).2.2) (fun i => hm _ (List.get_mem w i)) (mass_get_monotone hs) hf hL x
  rw [sum_get_map w (fun p => p.2.2^2),sum_get_map w (fun p => |p.2.2| * |p.2.1|)] at H
  exact H

theorem weightedAverage_bounded (w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈w,p.1∈Icc (0:ℝ) 1) (hs : w.Pairwise (fun p q => p.1≤q.1))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hL : LipschitzWith 1 f) :
    BoundedScalar (fun x => vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (x,0)) := by
  have H := (vectorIncrementAverage_regular w (hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ))
    (continuous_snd.pow 2) ((HasExpGrowth.linear (ContinuousLinearMap.snd ℝ ℝ ℝ)).pow 2)).1
  exact ⟨H.comp (continuous_id.prodMk continuous_const),weightedMomentBound w,
    weightedMomentBound_nonneg w,weightedAverage_abs_le w hm hs hf hL⟩

end SK.Analytic

end
end

end OAI
