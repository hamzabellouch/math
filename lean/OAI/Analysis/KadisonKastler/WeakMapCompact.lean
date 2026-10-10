import OAI.Analysis.KadisonKastler.CompleteWeakLimits
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! The completely bounded ball is compact in the pointwise weak operator topology. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance weakMapCompactOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance weakMapCompactStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

structure BoundedWeakAlgebraMap (M : VonNeumannAlgebra H) (c : ℝ) where
  map : Algebra M →ₗ[ℂ] Algebra M
  bound : CompletelyBoundedBy map c

def boundedWeakAlgebraCoefficients {M : VonNeumannAlgebra H} {c : ℝ}
    (F : BoundedWeakAlgebraMap M c) (t : Algebra M × H × H) : ℂ :=
  inner ℂ t.2.2 ((F.map t.1 : H →L[ℂ] H) t.2.1)

instance boundedWeakAlgebraMapTopology (M : VonNeumannAlgebra H) (c : ℝ) :
    TopologicalSpace (BoundedWeakAlgebraMap M c) :=
  TopologicalSpace.induced boundedWeakAlgebraCoefficients inferInstance

/-- All matrix bounds are retained at a pointwise weak cluster point. -/
theorem isCompact_boundedWeakAlgebraMap (M : VonNeumannAlgebra H) {c : ℝ} (hc : 0 ≤ c) :
    IsCompact (Set.univ : Set (BoundedWeakAlgebraMap M c)) := by
  apply isCompact_iff_ultrafilter_le_nhds.mpr
  intro ω _
  obtain ⟨L, hL, ht⟩ := exists_completelyBounded_weak_ultralimit M ω
    (fun F : BoundedWeakAlgebraMap M c => F.map) hc (fun F => F.bound)
  let l : BoundedWeakAlgebraMap M c := ⟨L, hL⟩
  refine ⟨l, Set.mem_univ _, ?_⟩
  have hcoeff : Tendsto boundedWeakAlgebraCoefficients (ω : Filter (BoundedWeakAlgebraMap M c))
      (𝓝 (boundedWeakAlgebraCoefficients l)) := by
    apply tendsto_pi_nhds.mpr
    intro t
    exact ht t.1 t.2.1 t.2.2
  change (ω : Filter (BoundedWeakAlgebraMap M c)) ≤
    @nhds _ (TopologicalSpace.induced boundedWeakAlgebraCoefficients inferInstance) l
  rw [nhds_induced]
  exact Filter.map_le_iff_le_comap.mp hcoeff

end

end KadisonKastler

end OAI
