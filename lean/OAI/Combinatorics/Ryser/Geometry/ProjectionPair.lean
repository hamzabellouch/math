import OAI.Combinatorics.Ryser.Geometry.AffineJoins
import OAI.Combinatorics.Ryser.Geometry.Cardinality
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Basic.Real.Basic

namespace OAI

namespace RyserCoveringCounterexample

open scoped BigOperators

variable {F : Type*} [Field F]

theorem projectionPair_bijective (d e : Direction F) (hne : d ≠ e) :
    Function.Bijective (fun p : Point F => (projection d p, projection e p)) := by
  constructor
  · intro p q hpq
    exact point_eq_of_projection_eq_of_ne_direction hne
      (congrArg Prod.fst hpq) (congrArg Prod.snd hpq)
  · intro z
    obtain ⟨p, hp, _⟩ :=
      existsUnique_incident_of_ne_direction (d, z.1) (e, z.2) hne
    exact ⟨p, Prod.ext hp.1 hp.2⟩

noncomputable def projectionPairEquiv (d e : Direction F) (hne : d ≠ e) :
    Point F ≃ F × F :=
  Equiv.ofBijective (fun p : Point F => (projection d p, projection e p))
    (projectionPair_bijective d e hne)

@[simp] theorem projectionPairEquiv_apply (d e : Direction F) (hne : d ≠ e)
    (p : Point F) :
    projectionPairEquiv d e hne p = (projection d p, projection e p) := rfl

theorem sum_projection_eq_indicator [Fintype F] [DecidableEq F]
    (p q : Point F) :
    (∑ d : Direction F, if projection d p = projection d q then (1 : ℝ) else 0) =
      if p = q then (Fintype.card F : ℝ) + 1 else 1 := by
  classical
  by_cases hpq : p = q
  · subst q
    simp [Nat.cast_add]
  · rw [ite_eq_right hpq]
    calc
      (∑ d : Direction F, if projection d p = projection d q then (1 : ℝ) else 0) =
          ∑ d : Direction F, if d = joinDirection p q then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        simp only [projection_eq_iff_eq_joinDirection hpq d]
      _ = 1 := Fintype.sum_ite_eq' _ _

end RyserCoveringCounterexample

end OAI
