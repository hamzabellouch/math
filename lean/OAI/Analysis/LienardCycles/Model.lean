import Mathlib

namespace OAI

namespace QuinticLienard

abbrev Plane := ℝ × ℝ

def vectorField (F : Polynomial ℝ) (z : Plane) : Plane :=
  (z.2 - F.eval z.1, -z.1)

def IsSolution (F : Polynomial ℝ) (z : ℝ → Plane) : Prop :=
  ∀ t : ℝ, HasDerivAt z (vectorField F (z t)) t

def IsPeriodicOrbit (F : Polynomial ℝ) (C : Set Plane) : Prop :=
  ∃ (z : ℝ → Plane) (T : ℝ),
    IsSolution F z ∧ 0 < T ∧ Function.Periodic z T ∧
    (∃ s t : ℝ, z s ≠ z t) ∧ C = Set.range z

def IsLimitCycle (F : Polynomial ℝ) (C : Set Plane) : Prop :=
  IsPeriodicOrbit F C ∧
    ∃ U : Set Plane, IsOpen U ∧ C ⊆ U ∧
      ∀ C' : Set Plane, IsPeriodicOrbit F C' → C' ⊆ U → C' = C

end QuinticLienard

end OAI
