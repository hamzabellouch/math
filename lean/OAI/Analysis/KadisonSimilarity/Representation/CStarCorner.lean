import OAI.Analysis.KadisonSimilarity.Derivation.TracialCornerCyclicity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

namespace OAI

/-! The actual unital C-star algebra cut out by a projection. Its identity
is the projection, and its norm is the ambient norm. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

def cstarCornerSubalgebra (e : P) (he : IsStarProjection e) : NonUnitalStarSubalgebra ℂ P where
  carrier := {a | e * a = a ∧ a * e = a}
  zero_mem' := by simp
  add_mem' ha hb := by
    exact ⟨by rw [mul_add, ha.1, hb.1], by rw [add_mul, ha.2, hb.2]⟩
  mul_mem' ha hb := by
    constructor
    · rw [← mul_assoc, ha.1]
    · rw [mul_assoc, hb.2]
  smul_mem' c a ha := by
    constructor
    · rw [mul_smul_comm, ha.1]
    · rw [smul_mul_assoc, ha.2]
  star_mem' ha := by
    constructor
    · simpa only [star_mul, he.isSelfAdjoint.star_eq] using congrArg star ha.2
    · simpa only [star_mul, he.isSelfAdjoint.star_eq] using congrArg star ha.1

instance cstarCornerSubalgebra_closed (e : P) (he : IsStarProjection e) :
    IsClosed (cstarCornerSubalgebra e he : Set P) :=
  (isClosed_eq (by fun_prop) continuous_id).inter (isClosed_eq (by fun_prop) continuous_id)

abbrev CStarCorner (e : P) (he : IsStarProjection e) := cstarCornerSubalgebra e he

namespace CStarCorner

variable (e : P) (he : IsStarProjection e)

instance : IsUnital (CStarCorner e he) := by
  refine ⟨⟨⟨e, he.isIdempotentElem.eq, he.isIdempotentElem.eq⟩, ?_⟩⟩
  intro a
  exact ⟨Subtype.ext a.property.1, Subtype.ext a.property.2⟩

instance : NormedRing (CStarCorner e he) := IsUnital.toNormedRing

instance : Algebra ℂ (CStarCorner e he) := Algebra.ofModule smul_mul_assoc mul_smul_comm

instance : NormedAlgebra ℂ (CStarCorner e he) where
  norm_smul_le := norm_smul_le

instance : CStarAlgebra (CStarCorner e he) where

instance : PartialOrder (CStarCorner e he) := CStarAlgebra.spectralOrder _

instance : StarOrderedRing (CStarCorner e he) := CStarAlgebra.spectralOrderedRing _

@[simp] theorem coe_one : ((1 : CStarCorner e he) : P) = e := by
  have h := congrArg (fun a : CStarCorner e he => (a : P))
    (one_mul (⟨e, he.isIdempotentElem.eq, he.isIdempotentElem.eq⟩ : CStarCorner e he))
  exact (1 : CStarCorner e he).property.2.symm.trans h

/-- Every ambient compression is an element of the corner. -/
def compress (a : P) : CStarCorner e he := ⟨e * a * e, by
  constructor
  · calc
      e * (e * a * e) = (e * e) * a * e := by noncomm_ring
      _ = e * a * e := by rw [he.isIdempotentElem.eq]
  · rw [mul_assoc, he.isIdempotentElem.eq]⟩

@[simp] theorem coe_compress (a : P) : (compress e he a : P) = e * a * e := rfl

theorem full : ∀ a : P, ∃ c : CStarCorner e he, (c : P) = e * a * e :=
  fun a => ⟨compress e he a, rfl⟩

end CStarCorner
end KadisonSimilarity

end

end OAI
