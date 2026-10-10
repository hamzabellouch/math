import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.MinimizingSubinterval
import OAI.Analysis.BiholderTransport.CostGeometry.DividedAction

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma minimizing_split_upper_support {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x) {s : ℝ} (hs : 0<s) (hs1 : s<1) (z : M) :
    cost z (riemannianExp x p) ≤ cost z (riemannianExp x (s • p))/s + (1-s)*‖p‖^2/2 := by
  have hseg : dist (riemannianExp x (s • p)) (riemannianExp x p) = (1-s)*‖p‖ := by
    rw [riemannianExp_smul,riemannianExp_eq_sprayFlow]
    have hh := sprayFlow_minimizing_subinterval (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)
      hs.le hs1.le (show dist x (sprayFlow 1 ⟨x,p⟩).1 = 1*‖p‖ by rw [one_mul,←riemannianExp_eq_sprayFlow]; exact hp)
    exact hh
  have hh := squared_dist_divided_action_le z (riemannianExp x (s • p)) (riemannianExp x p) hs hs1
  rw [hseg] at hh
  unfold cost
  convert hh using 1
  field_simp [hs.ne', (sub_pos.mpr hs1).ne']

lemma minimizing_split_contact {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x) {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    cost x (riemannianExp x (s • p))/s + (1-s)*‖p‖^2/2 = cost x (riemannianExp x p) := by
  have hsp := minimizingVectors_smul hp hs.le hs1.le
  unfold cost
  rw [hsp,hp,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
  field_simp [hs.ne']
  ring

end WeakMTWTransport

end

end OAI
