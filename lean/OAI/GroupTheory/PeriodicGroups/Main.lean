import Mathlib
import OAI.GroupTheory.PeriodicGroups.Periodicity.KernelTorsion

namespace OAI

namespace SourceBurnside.ConcreteSource

theorem kernel_torsion_reference (u : Steinberg 12 R)
    (hu : Elementary.representation u = 1) :
    ∃ m : ℕ, 0 < m ∧ u ^ m = 1 := kernel_torsion u hu

theorem periodic_reference : Periodic (Steinberg 12 R) := steinberg_periodic

end SourceBurnside.ConcreteSource

namespace SourceBurnside

theorem thm_main : MainStatement ∧ BurnsideStatement :=
  ⟨ConcreteSource.main_statement, ConcreteSource.burnside_statement⟩

end SourceBurnside

end OAI
