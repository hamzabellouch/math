import Mathlib
import OAI.Combinatorics.KMedian.Projection.IncidenceOperator
import OAI.Combinatorics.KMedian.Projection.Rounding
import OAI.Combinatorics.KMedian.Projection.Repeat

namespace OAI

section Inline_PCPFixedImpossible

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection

def impossible : BiProjection Bool Bool Bool Bool Bool Bool where
  edge := Equiv.prodComm Bool Bool
  project p a := if p.1 && p.2 then !a else a

lemma impossible_consistent : impossible.Consistent := by
  intro u d e h a
  change d=e at h
  subst e
  rfl

lemma impossible_sound : impossible.Sound (3/4) := by
  intro a b
  unfold score
  rw [expect_bool]
  simp_rw [expect_bool]
  have ha0 : a false=false ∨ a false=true := (Bool.eq_false_or_eq_true _).symm
  have ha1 : a true=false ∨ a true=true := (Bool.eq_false_or_eq_true _).symm
  have hb0 : b false=false ∨ b false=true := (Bool.eq_false_or_eq_true _).symm
  have hb1 : b true=false ∨ b true=true := (Bool.eq_false_or_eq_true _).symm
  rcases ha0 with h0|h0 <;> rcases ha1 with h1|h1 <;>
    rcases hb0 with h2|h2 <;> rcases hb1 with h3|h3 <;>
    norm_num [impossible,h0,h1,h2,h3]

lemma impossible_expands : impossible.Expands (1/4) := by
  intro f
  have he : impossible.average f=fun _ => 𝔼 u, f u := rfl
  rw [he]
  have hm := mean_sq_le_energy f
  simp only [energy,Fintype.expect_const]
  unfold energy at hm
  linarith

lemma impossible_bound : impossible.CollisionBound (1-(1:ℝ)/1024) := by
  have h := impossible.collisionBound_of_expansion (3/4) (1/4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) impossible_sound impossible_expands
  norm_num at h ⊢
  exact h
end BiProjection
end MetricKMedian.PCP

end Inline_PCPFixedImpossible

end OAI
