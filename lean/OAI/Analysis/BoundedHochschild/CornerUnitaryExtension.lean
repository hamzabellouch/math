import OAI.Analysis.BoundedHochschild.Corners

namespace OAI

/-! Extending corner unitaries by the identity on the complementary corner. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma corner_complement_left {p : M} (hp : IsStarProjection p) (a : Corner p hp) :
    (1 - p) * (a : M) = 0 := by
  rw [sub_mul, one_mul, a.property.1, sub_self]

omit [PartialOrder M] [StarOrderedRing M] in
lemma corner_complement_right {p : M} (hp : IsStarProjection p) (a : Corner p hp) :
    (a : M) * (1 - p) = 0 := by
  rw [mul_sub, mul_one, a.property.2, sub_self]

omit [PartialOrder M] [StarOrderedRing M] in
lemma cornerUnitaryExtension_mem {p : M} (hp : IsStarProjection p) (u : unitary (Corner p hp)) :
    (((u : Corner p hp) : M) + (1 - p)) ∈ unitary M := by
  let a : M := ((u : Corner p hp) : M)
  have hstar : star a * a = p := congrArg Subtype.val (Unitary.coe_star_mul_self u)
  have hmul : a * star a = p := congrArg Subtype.val (Unitary.coe_mul_star_self u)
  have hleft : (1 - p) * a = 0 := corner_complement_left hp (u : Corner p hp)
  have hright : a * (1 - p) = 0 := corner_complement_right hp (u : Corner p hp)
  have hstarleft : (1 - p) * star a = 0 := corner_complement_left hp (star (u : Corner p hp))
  have hstarright : star a * (1 - p) = 0 := corner_complement_right hp (star (u : Corner p hp))
  constructor
  · change star (a + (1 - p)) * (a + (1 - p)) = 1
    rw [star_add, hp.one_sub.isSelfAdjoint.star_eq, add_mul, mul_add, mul_add,
      hstar, hstarright, hleft, hp.one_sub.isIdempotentElem.eq]
    abel
  · change (a + (1 - p)) * star (a + (1 - p)) = 1
    rw [star_add, hp.one_sub.isSelfAdjoint.star_eq, add_mul, mul_add, mul_add,
      hmul, hright, hstarleft, hp.one_sub.isIdempotentElem.eq]
    abel

def cornerUnitaryExtension {p : M} (hp : IsStarProjection p) :
    unitary (Corner p hp) →* unitary M where
  toFun u := ⟨_, cornerUnitaryExtension_mem hp u⟩
  map_one' := Subtype.ext (by change p + (1 - p) = 1; abel)
  map_mul' u v := by
    apply Subtype.ext
    change (((u : Corner p hp) : M) * ((v : Corner p hp) : M)) + (1 - p) =
      (((u : Corner p hp) : M) + (1 - p)) * (((v : Corner p hp) : M) + (1 - p))
    rw [add_mul, mul_add, mul_add, corner_complement_right hp, corner_complement_left hp,
      hp.one_sub.isIdempotentElem.eq]
    abel

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma cornerUnitaryExtension_apply {p : M} (hp : IsStarProjection p)
    (u : unitary (Corner p hp)) :
    (cornerUnitaryExtension hp u : M) = ((u : Corner p hp) : M) + (1 - p) := rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
