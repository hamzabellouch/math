import Mathlib
import OAI.Probability.CriticalPercolation.GraphTopology.GraphAutomorphismTopology
import OAI.Probability.CriticalPercolation.GraphGeometry.NormalOrbitAction
import OAI.Probability.CriticalPercolation.GraphGeometry.LocallyConnectedActionKernel
import OAI.Probability.CriticalPercolation.GraphTopology.LocallyCompactSubgroup
import OAI.Probability.CriticalPercolation.GraphTopology.OpenNormalCore

namespace OAI

section
noncomputable section
open Set Function Topology

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)
variable [TopologicalSpace X] [DiscreteTopology X]
local instance subgroupOrbitKernelAutTopology : TopologicalSpace (Γ ≃g Γ) := autTopology Γ

theorem compact_open_normal_of_finiteIndex_subquotient
    (L : Subgroup (Γ ≃g Γ)) [L.FiniteIndex] (H : Subgroup L) [H.Normal]
    (hH : IsCompact (H : Set L))
    [LocallyCompactSpace (L ⧸ H)] [LocallyConnectedSpace (L ⧸ H)] :
    ∃ J : Subgroup (Γ ≃g Γ), J.Normal ∧
      IsCompact (J : Set (Γ ≃g Γ)) ∧ IsOpen (J : Set (Γ ≃g Γ)) := by
  have hL : IsOpen (L : Set (Γ ≃g Γ)) :=
    CompactQuotient.open_of_finiteIndex_compact_kernel_locallyCompact_quotient L H hH
  let B := NormalOrbit.Blocks (X := X) H
  let _ : TopologicalSpace B := ⊥
  let _ : DiscreteTopology B := ⟨rfl⟩
  let f := NormalOrbit.blockHom (X := X) H
  have hcont : ∀ b : B, Continuous (fun l : L => f l b) := by
    intro b
    induction b using Quotient.inductionOn with
    | h x =>
      change Continuous (fun l : L => NormalOrbit.block H ((l : Γ ≃g Γ) x))
      exact (continuous_of_discreteTopology : Continuous (NormalOrbit.block (X := X) H)).comp
        ((continuous_eval Γ x).comp continuous_subtype_val)
  have hopen := ConnectedAction.open_kernel_of_locallyConnected_quotient f hcont H
    (NormalOrbit.le_ker_blockHom H)
  let J := f.ker.map L.subtype
  have hJo : IsOpen (J : Set (Γ ≃g Γ)) := hL.isOpenMap_subtype_val _ hopen
  have hJc : IsClosed (J : Set (Γ ≃g Γ)) := J.isClosed_of_isOpen hJo
  have hfin : ∀ x : X, (MulAction.orbit H x).Finite := by
    intro x
    have hc := hH.image ((continuous_eval Γ x).comp continuous_subtype_val)
    apply (isCompact_iff_finite.mp hc).subset
    rintro y ⟨h,rfl⟩
    exact ⟨h.val,h.property,rfl⟩
  have hmem : ∀ g∈J, ∀ x, g x∈MulAction.orbit H x := by
    rintro _ ⟨l,hl,rfl⟩ x
    have hh := congrArg (fun p : Equiv.Perm B => p (NormalOrbit.block H x)) hl
    exact (NormalOrbit.block_eq_iff H _ x).mp hh
  have hJcomp : IsCompact (J : Set (Γ ≃g Γ)) := by
    apply (compact_coordinate_bounds Γ (MulAction.orbit H) hfin).of_isClosed_subset hJc
    intro g hg
    exact ⟨hmem g hg,hmem g⁻¹ (J.inv_mem hg)⟩
  have hn : L≤Subgroup.normalizer (J : Set (Γ ≃g Γ)) := by
    have hh := f.ker.le_normalizer_map L.subtype
    simpa only [Subgroup.normalizer_eq_top,←MonoidHom.range_eq_map,Subgroup.range_subtype] using hh
  let _ : (Subgroup.normalizer (J : Set (Γ ≃g Γ))).FiniteIndex :=
    Subgroup.finiteIndex_of_le hn
  have hc := CompactQuotient.compact_open_normalCore_of_finiteIndex_normalizer J hJcomp hJo
  exact ⟨J.normalCore,inferInstance,hc⟩

end CriticalPercolation.GraphTopology
end
end

end OAI
