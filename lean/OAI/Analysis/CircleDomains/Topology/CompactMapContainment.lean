import Mathlib.Topology.CompactOpen

namespace OAI

/-! Compact-open convergence retains containment of each fixed compact
set in an open neighborhood of its limiting image. -/
open Set Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma eventually_mapsTo_of_compact_convergence
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : ℕ → C(X, Y)} {g : C(X, Y)}
    (hf : Tendsto f atTop (𝓝 g)) {K : Set X} (hK : IsCompact K)
    {U : Set Y} (hU : IsOpen U) (h : MapsTo g K U) :
    ∀ᶠ n in atTop, MapsTo (f n) K U :=
  hf.eventually (ContinuousMap.eventually_mapsTo hK hU h)

end CircleDomainRigidity

end

end OAI
