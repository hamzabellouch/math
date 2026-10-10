import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.GroupTheory.Perm.Basic

namespace OAI

namespace Invariant233

variable {X Y : Type*} [MeasurableSpace Y]

@[reducible] def orbitMeasurableSpace (σ : Equiv.Perm X) (f : X → Y) : MeasurableSpace X :=
  ⨆ n : ℤ, MeasurableSpace.comap (fun x => f ((σ ^ n) x)) ‹MeasurableSpace Y›

end Invariant233

end OAI
