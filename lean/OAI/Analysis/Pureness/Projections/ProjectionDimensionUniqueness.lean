import OAI.Analysis.Pureness.Projections.ProjectionDimension
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace OAI
noncomputable section
namespace CuntzPureness
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem exists_projection_dimension_sum_carry
    (hcomp : ∀ p q : D, IsStarProjection p → IsStarProjection q →
      (∃ v, star v*v=p ∧ IsStarProjection (v*star v) ∧ v*star v ≤ q) ∨
      (∃ v, star v*v=q ∧ IsStarProjection (v*star v) ∧ v*star v ≤ p))
    (p q : D) (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ r : D, IsStarProjection r ∧ ∃ k : ℕ, ∀ d : ProjectionDimension D,
      d r+(k:ℝ)=d p+d q := by
  rcases hcomp p (1-q) hp hq.one_sub with ⟨v,he,hg,hgq⟩ | ⟨v,he,hg,hgp⟩
  · have ho := projection_residual_orthogonal (IsStarProjection.one D) hq hg
      (sub_nonneg.mp hq.one_sub.nonneg) hgq
    refine ⟨q+v*star v,projection_add_of_orthogonal hq hg ho.1 ho.2,0,?_⟩
    intro d
    have hd := d.polar v (he.symm ▸ hp)
    rw [he] at hd
    rw [Nat.cast_zero,add_zero,d.add q _ hq hg ho.1,← hd,add_comm]
  · refine ⟨p-v*star v,(hg.le_iff_sub hp).mp hgp,1,?_⟩
    intro d
    have hd := d.polar v (he.symm ▸ hq.one_sub)
    rw [he,d.one_sub hq] at hd
    rw [d.sub hp hg hgp,Nat.cast_one,← hd]
    ring

theorem exists_projection_dimension_multiple_remainder
    (hcomp : ∀ p q : D, IsStarProjection p → IsStarProjection q →
      (∃ v, star v*v=p ∧ IsStarProjection (v*star v) ∧ v*star v ≤ q) ∨
      (∃ v, star v*v=q ∧ IsStarProjection (v*star v) ∧ v*star v ≤ p))
    (p : D) (hp : IsStarProjection p) (n : ℕ) :
    ∃ r : D, IsStarProjection r ∧ ∃ k : ℕ, ∀ d : ProjectionDimension D,
      d r+(k:ℝ)=(n:ℝ)*d p := by
  induction n with
  | zero =>
    exact ⟨0,IsStarProjection.zero D,0,fun d => by rw [d.map_zero]; simp⟩
  | succ n ih =>
    obtain ⟨r,hr,k,hk⟩ := ih
    obtain ⟨s,hs,j,hj⟩ := exists_projection_dimension_sum_carry hcomp p r hp hr
    refine ⟨s,hs,k+j,?_⟩
    intro d
    have hk' := hk d
    have hj' := hj d
    rw [Nat.cast_add,Nat.cast_succ]
    nlinarith

theorem projection_dimension_unique
    (hcomp : ∀ p q : D, IsStarProjection p → IsStarProjection q →
      (∃ v, star v*v=p ∧ IsStarProjection (v*star v) ∧ v*star v ≤ q) ∨
      (∃ v, star v*v=q ∧ IsStarProjection (v*star v) ∧ v*star v ≤ p))
    (d t : ProjectionDimension D) (p : D) (hp : IsStarProjection p) : d p=t p := by
  have hle (d t : ProjectionDimension D) : d p ≤ t p := by
    by_contra h
    have hc : 0 < d p-t p := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨n,hn⟩ := exists_nat_gt (1/(d p-t p))
    have hbig : 1 < (n:ℝ)*(d p-t p) := (div_lt_iff₀ hc).mp hn
    obtain ⟨r,hr,k,hk⟩ := exists_projection_dimension_multiple_remainder hcomp p hp n
    have hd := hk d
    have ht := hk t
    have hd1 := d.le_one hr
    have ht0 := t.nonneg r hr
    nlinarith
  exact le_antisymm (hle d t) (hle t d)
end CuntzPureness

end

end OAI
