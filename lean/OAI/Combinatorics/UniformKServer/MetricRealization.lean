import Mathlib
import OAI.Combinatorics.UniformKServer.Basic

namespace OAI

                                        
section

/-! The exact rational input metric realized as Mathlib's metric; no geometry
assumptions are added at the interface. -/
namespace UniformKServer.RationalMetric
variable {n : ℕ}

@[instance_reducible] def metric (d : RationalMetric n) : MetricSpace (Fin n) where
  dist x y := (d.distance x y : ℝ)
  dist_self x := by exact_mod_cast (d.eq_zero x x).mpr rfl
  dist_comm x y := by exact_mod_cast d.symm x y
  dist_triangle x y z := by exact_mod_cast d.triangle x y z
  eq_of_dist_eq_zero := by
    intro x y h
    exact (d.eq_zero x y).mp (by exact_mod_cast h)

end UniformKServer.RationalMetric

end


end OAI
