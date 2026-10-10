import OAI.Analysis.Pureness.Cuntz.CuntzSubequivalence
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

namespace OAI
namespace CuntzPureness
open Filter Topology
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem cstar_cuntzSubequiv_refl (a : A) : CuntzSubequiv a a := by
  apply (cuntzSubequiv_iff_norm a a).mpr
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  let l := CStarAlgebra.approximateUnit A
  have hu := CStarAlgebra.increasingApproximateUnit A
  have hleft : ∀ᶠ e in l, ‖a - a * e‖ < ε / 2 := by
    have h := (hu.tendsto_mul_left a).eventually (Metric.ball_mem_nhds a hε2)
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using h
  have hright : ∀ᶠ e in l, ‖a - e * a‖ < ε / 2 := by
    have h := (hu.tendsto_mul_right a).eventually (Metric.ball_mem_nhds a hε2)
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using h
  obtain ⟨e, he1, he2, hen, hestar⟩ :=
    (hleft.and (hright.and (hu.eventually_norm.and hu.eventually_star_eq))).exists
  refine ⟨e, ?_⟩
  have heq : a - star e * a * e = (a - a * e) + (a - e * a) * e := by
    rw [hestar]
    noncomm_ring
  calc
    ‖a - star e * a * e‖ = ‖(a - a * e) + (a - e * a) * e‖ := by rw [heq]
    _ ≤ ‖a - a * e‖ + ‖(a - e * a) * e‖ := norm_add_le _ _
    _ ≤ ‖a - a * e‖ + ‖a - e * a‖ * ‖e‖ :=
      add_le_add le_rfl (norm_mul_le _ _)
    _ ≤ ‖a - a * e‖ + ‖a - e * a‖ := by
      apply add_le_add le_rfl
      nlinarith [norm_nonneg (a - e * a)]
    _ < ε := by linarith

def positiveCuntzSetoid : Setoid {a : A // 0 ≤ a} where
  r a b := CuntzSubequiv a.val b.val ∧ CuntzSubequiv b.val a.val
  iseqv := {
    refl := fun a => ⟨cstar_cuntzSubequiv_refl a.val, cstar_cuntzSubequiv_refl a.val⟩
    symm := fun h => h.symm
    trans := fun h₁ h₂ => ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩ }

def PositiveCuntzClass (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] := Quotient (positiveCuntzSetoid (A := A))
end CuntzPureness

end OAI
