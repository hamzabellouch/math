import OAI.Analysis.BoundedHochschild.Conditional

namespace OAI

/-!
# Type I structure of abelian algebras

Every projection in an abelian C⋆-algebra has a commutative corner. Therefore
an abelian algebra, as well as each of its central corners, has no nonzero
type II₁ summand. This verifies the structural hypothesis of the classical
vanishing input for the abelian case.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners

variable {M : Type*} [CommCStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- A corner of a commutative C⋆-algebra is commutative. -/
instance commutativeCorner (p : M) (hp : IsStarProjection p) :
    CommCStarAlgebra (Corner p hp) where
  mul_comm a b := Subtype.ext (mul_comm (a : M) (b : M))

omit [PartialOrder M] [StarOrderedRing M] in
/-- Every projection in a commutative algebra is abelian. -/
lemma abelian_projection {p : M} (hp : IsStarProjection p) :
    PopaTypeII.AbelianProjection hp := by
  intro a b
  exact Subtype.ext (mul_comm (a : M) (b : M))

omit [StarOrderedRing M] in
/-- Every projection in a commutative algebra has a type I corner. -/
lemma abelian_typeICorner {z : M} (hz : IsStarProjection z) :
    PopaTypeII.TypeICorner hz := by
  intro p hp _ hp0
  exact ⟨p, hp, le_rfl, hp0, abelian_projection hp⟩

/-- A commutative C⋆-algebra has no type II₁ central summand. -/
theorem abelian_noTypeII1Summand : NoTypeII1Summand M := by
  intro z hz _hc _hfinite hnoI
  by_contra hz0
  let N := Corner z hz
  have hN1 : (1 : N) ≠ 0 := by
    intro hzero
    apply hz0
    exact congrArg (fun a : N => (a : M)) hzero
  exact hnoI 1 (IsStarProjection.one N) (fun _ => Commute.one_left _) hN1
    (abelian_typeICorner (IsStarProjection.one N))

end KadisonRingrose
end BoundedHochschild

end

end OAI
