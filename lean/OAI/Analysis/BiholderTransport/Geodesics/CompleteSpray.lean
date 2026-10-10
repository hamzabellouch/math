import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.CompactDisk
import OAI.Analysis.BiholderTransport.LocalFlow.CompactFlow
import OAI.Analysis.BiholderTransport.Geodesics.SprayEnergy
import OAI.Analysis.BiholderTransport.Regularity.BundleSeparation
import OAI.Analysis.BiholderTransport.Calculus.RiemannianContinuous

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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma exists_complete_spray_curve (z : TangentBundle 𝓘(ℝ,E) M) :
    ∃ γ : ℝ → TangentBundle 𝓘(ℝ,E) M, γ 0 = z ∧
      IsMIntegralCurve γ (geodesicSpray (E := E)) := by
  have : T2Space (TangentBundle 𝓘(ℝ,E) M) := bundle_totalSpace_t2
  have : IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,E))
  apply exists_complete_curve_of_compact_invariant contMDiff_geodesicSpray
    (isCompact_bundle_disk (F := E) (E := fun x : M => TangentSpace 𝓘(ℝ,E) x) ‖z.2‖)
    _ z (Set.mem_ofPred.mpr le_rfl)
  intro a γ hγ0 hγ t ht
  have ha : 0 < a := by obtain ⟨h₁,h₂⟩ := ht; linarith
  change ‖(γ t).2‖ ≤ ‖z.2‖
  rw [spray_speed_constant hγ ht ⟨neg_lt_zero.mpr ha,ha⟩]
  exact hγ0

end WeakMTWTransport

end

end OAI
