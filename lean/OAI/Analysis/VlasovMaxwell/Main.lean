import Mathlib
import OAI.Analysis.VlasovMaxwell.LocalPDE.GeometryCutoffDeficitLogSum
import OAI.Analysis.VlasovMaxwell.LocalPDE.SmoothLocalExistence
import OAI.Analysis.VlasovMaxwell.Continuation.PrefixUniqueness
import OAI.Analysis.VlasovMaxwell.Continuation.GlobalContinuation
import OAI.Analysis.VlasovMaxwell.Population.MagneticEstimates
import OAI.Analysis.VlasovMaxwell.Population.BulkSpatialUniform
import OAI.Analysis.VlasovMaxwell.Population.BulkReceiverScalar
import OAI.Analysis.VlasovMaxwell.Population.SelectedRemainder
import OAI.Analysis.VlasovMaxwell.Population.BulkWeightCost
import OAI.Analysis.VlasovMaxwell.Population.DirectExpandedLargeAngular
import OAI.Analysis.VlasovMaxwell.Population.DirectExpandedDeficitUniform
import OAI.Analysis.VlasovMaxwell.Population.DirectExpandedAssemble
import OAI.Analysis.VlasovMaxwell.Population.DirectExpandedTransportNear
import OAI.Analysis.VlasovMaxwell.Population.BulkReceiverResidual
import OAI.Analysis.VlasovMaxwell.Retarded.DirectMixedCover
import OAI.Analysis.VlasovMaxwell.Population.GoodSharedEstimates
import OAI.Analysis.VlasovMaxwell.Retarded.DirectSmallAbsolute
import OAI.Analysis.VlasovMaxwell.Retarded.DirectLorentzUniform

namespace OAI

/-! Global classical solvability and uniqueness for smooth admissible data. -/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma Admissible.uniform_physical_population_increment {d : Datum} (hd : Admissible d)
    (H : ℝ) :
    ∃ M A P₀ : ℝ, 0 < M ∧ 0 < A ∧
      ∀ U : ℝ, 0 < U → U ≤ H → ∀ s : Solution,
      BoundedClassicalPrefix d s U → ∀ F : PhaseFlowOn s.E s.B U,
        PopulationIncrement (fun z t => (F.flow z t).2) (tsupport d.f₀) U M A P₀ := by
  obtain ⟨M, A, P₀, hM, hA, hP₀, hinc⟩ := hd.population_increment H
  refine ⟨M, A, P₀, hM, hA, ?_⟩
  intro U hU hUH s hs F
  apply hinc s U F.flow hUH
  intro τ hτ
  exact ⟨hs.classical.restrict hτ.2.le, F.restrict hτ.2.le, rfl⟩

theorem global_classical_solution (d : Datum) (hd : Admissible d) :
    ∃ s : Solution, Classical d s ∧ SmoothOnFiniteHorizons s ∧
      ∀ s' : Solution, Classical d s' → SameNonnegativeTime s s' := by
  exact global_classical_of_uniform_physical_increment hd
    (fun H _ => hd.uniform_physical_population_increment H)

end RVM

end

end OAI
