import OAI.Analysis.CircleDomains.Topology.CompactLocalPathConnectivity
import OAI.Analysis.CircleDomains.Topology.LooplessSeparatingCoordinate
import OAI.Analysis.CircleDomains.Topology.RealCoordinateSimplePath
import OAI.Analysis.CircleDomains.Probability.ArcNullImage

namespace OAI

/-! Small path approximations give local path connectivity; minimization of interval oscillations erases loops,
and a monotone separating coordinate removes the remaining constant pauses. -/
open Set Function
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

lemma exists_injective_subpath {X : Type*} [MetricSpace X] [CompleteSpace X]
    {x y : X} (γ : Path x y) (hne : x ≠ y) :
    ∃ β : Path x y, Injective β ∧ range β ⊆ range γ := by
  obtain ⟨g, hg, hloop⟩ := exists_loopless_path γ.toContinuousMap
  have hg0 : g 0 = x := hg.1.trans γ.source
  have hg1 : g 1 = y := hg.2.1.trans γ.target
  have hgne : g 0 ≠ g 1 := fun h => hne (hg0.symm.trans (h.trans hg1))
  obtain ⟨β, hβinj, hβrange⟩ := simplePath_of_real_coordinate g (looplessCoordinate g)
    (looplessCoordinate_mono g) (looplessCoordinate_fibers g hloop) hgne
  refine ⟨β.cast hg0.symm hg1.symm, hβinj, ?_⟩
  exact hβrange.trans hg.2.2.1

/-- Lorimer's connected-open simple-arc specialization. -/
theorem hasSimpleArcsInConnectedOpens_compact_metric
    (X : Type*) [MetricSpace X] [CompactSpace X] [LocallyConnectedSpace X] :
    HasSimpleArcsInConnectedOpens X := by
  intro U hU hconn x hx y hy hne
  obtain ⟨γ, hγ⟩ := (compact_metric_connected_open_paths X hU hconn).joinedIn x hx y hy
  obtain ⟨β, hβinj, hβrange⟩ := exists_injective_subpath γ hne
  exact ⟨β, hβinj, hβrange.trans (range_subset_iff.mpr hγ)⟩

end CircleDomainRigidity

end

end OAI
