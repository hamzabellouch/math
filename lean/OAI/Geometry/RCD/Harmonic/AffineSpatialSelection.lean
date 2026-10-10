import OAI.Geometry.RCD.Transport.FirstOrderNearbyPlanErrors

namespace OAI

/-! # Selecting paths with small uniform affine error and small spatial cost -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem affine_spatial_selection {n : ℕ} (π : ℕ → Measure C(Time,X))
    [∀ k, IsProbabilityMeasure (π k)]
    (F : ℕ → Fin n → C(Time,X) → C(Time,ℝ)) (E : ℕ → X → ℝ)
    (hE : ∀ k z, 0 ≤ E k z)
    (hI : ∀ k, Integrable (affineSpatialPathCost (F k) (E k)) (π k))
    (hlim : Tendsto (fun k => ∫ γ, affineSpatialPathCost (F k) (E k) γ ∂π k) atTop (𝓝 0))
    (P : ℕ → C(Time,X) → Prop) (hP : ∀ k, ∀ᵐ γ ∂π k, P k γ) :
    ∃ (γ : ℕ → C(Time,X)) (a : ℕ → ℝ),
      (∀ k, P k (γ k)) ∧ (∀ k, 0 ≤ a k) ∧ Tendsto a atTop (𝓝 0) ∧
      (∀ k i (t : Time), |F k i (γ k) t| ≤ a k) ∧
      (∀ k, (∫ t in Icc (0:ℝ) 1, E k (geodesicExtension (γ k) t)) ≤ a k) := by
  classical
  let a k := ∫ γ, affineSpatialPathCost (F k) (E k) γ ∂π k
  have hpos (k : ℕ) (γ : C(Time,X)) : 0 ≤ affineSpatialPathCost (F k) (E k) γ :=
    add_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (integral_nonneg (fun _ => hE k _))
  have hex (k : ℕ) : ∃ γ, P k γ ∧ affineSpatialPathCost (F k) (E k) γ ≤ a k := by
    obtain ⟨γ,hγ,hb⟩ := exists_notMem_null_le_integral (hI k) (ae_iff.mp (hP k))
    exact ⟨γ,of_not_not hγ,hb⟩
  choose γ hgood hbound using hex
  refine ⟨γ,a,hgood,fun k => integral_nonneg (hpos k),hlim,?_,?_⟩
  · intro k i t
    have hi : ‖F k i (γ k)‖ ≤ ∑ j, ‖F k j (γ k)‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (F k j (γ k))) (Finset.mem_univ i)
    have ht : |F k i (γ k) t| ≤ ‖F k i (γ k)‖ := (F k i (γ k)).norm_coe_le_norm t
    have he : 0 ≤ ∫ s in Icc (0:ℝ) 1, E k (geodesicExtension (γ k) s) :=
      integral_nonneg (fun _ => hE k _)
    exact (ht.trans hi).trans (le_trans (le_add_of_nonneg_right he) (hbound k))
  · intro k
    exact (le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).trans (hbound k)

end RegularPointCoordinates

end

end OAI
