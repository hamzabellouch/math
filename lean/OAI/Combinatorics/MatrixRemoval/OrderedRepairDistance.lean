import OAI.Combinatorics.MatrixRemoval.OrderedSampledSelection
import OAI.Combinatorics.MatrixRemoval.HostRepairDistance

namespace OAI

/-!
# Unconditional repair lower bound for the ordered canonical host

The sampler order certificate follows from the independent increasing
row and column enumerations, giving the arbitrary-repair lower bound.
-/

noncomputable section
namespace Problem348.OrderedHost

open Construction

/-- Every fixedH-free repair of the actual ordered host changes at least m²
cells. In particular no pinning premise or preservation condition is assumed. -/
theorem hammingDistance_ge {h : ℕ} (hh : 1 ≤ h)
    (B : BinaryMatrix (size h)) (hfree : HFree fixedH B) :
    (2 ^ h) ^ 2 ≤
      hammingDistance (SelectedAnchor.matrix (rowIndex h) (columnIndex h)) B :=
  SampledSelection.hammingDistance_ge hh (rowIndex h) (columnIndex h)
    (sampledAxisConditions h) B hfree

/-- The concrete three-seed sampler has the exact uniform guard bound. -/
theorem sampledSelection_guard_frequency {h : ℕ} (hh : 1 ≤ h)
    (rc : Fin (size h) × Fin (size h)) :
    (Finset.univ.filter fun s : TreeSampling.Seeds (2 ^ h) =>
      rc ∈ (sampledSelection hh s.1 s.2.1 s.2.2).guards h).card * (2 ^ h) ^ 2 ≤
        Fintype.card (TreeSampling.Seeds (2 ^ h)) :=
  SampledSelection.selection_guard_frequency hh (rowIndex h) (columnIndex h)
    (sampledAxisConditions h) rc

end Problem348.OrderedHost

end

end OAI
