import OAI.Combinatorics.Crossing.DrawingDefinition
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Separation.Hausdorff

namespace OAI

namespace Zarankiewicz

theorem path_range_eq_of_subset {a b : Plane} (γ δ : Path a b)
    (hγ : Function.Injective γ) (hsub : Set.range δ ⊆ Set.range γ) :
    Set.range δ=Set.range γ := by
  apply Set.Subset.antisymm hsub
  rintro x ⟨t,rfl⟩
  have hc : IsPreconnected (γ ⁻¹' Set.range δ) :=
    (isPreconnected_range δ.continuous).preimage_of_isClosedMap hγ γ.continuous.isClosedMap hsub
  have h0 : (0 : unitInterval) ∈ γ ⁻¹' Set.range δ := ⟨0,δ.source.trans γ.source.symm⟩
  have h1 : (1 : unitInterval) ∈ γ ⁻¹' Set.range δ := ⟨1,δ.target.trans γ.target.symm⟩
  exact hc.Icc_subset h0 h1 t.property

end Zarankiewicz

end OAI
