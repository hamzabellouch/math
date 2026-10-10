import OAI.Analysis.Pureness.Projections.QuotientMaximalMatch

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace
open scoped ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

include hsqrt in

theorem quotient_projection_comparison
    (hlocal : ∀ p q : T.CauchyQuotient hadd,
      IsStarProjection p → IsStarProjection q → p ≠ 0 → q ≠ 0 →
      ∃ v, IsStarProjection (star v*v) ∧ IsStarProjection (v*star v) ∧
        star v*v ≠ 0 ∧ v*star v ≠ 0 ∧ star v*v ≤ q ∧ v*star v ≤ p)
    (p q : T.CauchyQuotient hadd) (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (∃ v, star v*v=p ∧ IsStarProjection (v*star v) ∧ v*star v ≤ q) ∨
    (∃ v, star v*v=q ∧ IsStarProjection (v*star v) ∧ v*star v ≤ p) := by
  obtain ⟨u,hmax⟩ := T.exists_quotient_maximal_match hadd hsqrt hp hq
  have hexhaust : u.val*star u.val=p ∨ star u.val*u.val=q := by
    by_contra hn
    obtain ⟨hgp,heq⟩ := not_or.mp hn
    have hpr := (u.range.le_iff_sub hp).mp u.range_le
    have hqr := (u.initial.le_iff_sub hq).mp u.initial_le
    obtain ⟨z,hzi,hzr,hzi0,_,hziq,hzrp⟩ := hlocal _ _ hpr hqr
      (fun h => hgp (sub_eq_zero.mp h).symm) (fun h => heq (sub_eq_zero.mp h).symm)
    let z' : ProjectionMatch (p-u.val*star u.val) (q-star u.val*u.val) :=
      ⟨z,hzi,hzr,hziq,hzrp⟩
    obtain ⟨v,huv,_,hi⟩ := ProjectionMatch.exists_extension hp hq u z'
    have hvu : v=u := le_antisymm (hmax v huv) huv
    rw [hvu] at hi
    have hz : star z*z=0 := by
      change star u.val*u.val=star u.val*u.val+star z*z at hi
      exact (add_left_cancel (hi.symm.trans (add_zero _).symm))
    exact hzi0 hz
  rcases hexhaust with hg | he
  · left
    refine ⟨star u.val,?_,?_,?_⟩
    · simpa only [star_star] using hg
    · simpa only [star_star] using u.initial
    · simpa only [star_star] using u.initial_le
  · exact Or.inr ⟨u.val,he,u.range,u.range_le⟩

include hsqrt in

theorem quotient_projection_subequivalent_of_value_le
    (hcomp : ∀ p q : T.CauchyQuotient hadd, IsStarProjection p → IsStarProjection q →
      (∃ v, star v*v=p ∧ IsStarProjection (v*star v) ∧ v*star v ≤ q) ∨
      (∃ v, star v*v=q ∧ IsStarProjection (v*star v) ∧ v*star v ≤ p))
    (p q : T.CauchyQuotient hadd) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hle : (T.quotientValue hadd hsqrt p).re ≤ (T.quotientValue hadd hsqrt q).re) :
    ∃ v, star v*v=p ∧ IsStarProjection (v*star v) ∧ v*star v ≤ q := by
  rcases hcomp p q hp hq with h | ⟨v,hvi,hvr,hvp⟩
  · exact h
  · have he : v*star v=p := T.quotient_projection_eq_of_le_of_value_le hadd hsqrt hvr hp hvp (by
      have ht := congrArg Complex.re (T.quotientValue_polar hadd hsqrt v)
      rw [hvi] at ht
      exact hle.trans_eq ht)
    refine ⟨star v,?_,?_,?_⟩
    · simpa only [star_star] using he
    · simpa only [star_star,hvi] using hq
    · simp only [star_star,hvi,le_refl]
end CuntzPureness.PositiveQuasitrace

end

end OAI
