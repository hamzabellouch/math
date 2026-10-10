import OAI.Combinatorics.EditApproximation.Geometry.CanonicalFractionWork
import OAI.Combinatorics.EditApproximation.Binary.UnreducedOptimizer
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The optimizer's numerical loops executed on Boolean fraction storage.
The value proofs identify the unreduced numerator and denominator, not just
the represented rational. Thus the raw storage bounds apply to this code. -/

namespace EditApproximation
namespace BinaryFraction

@[simp] theorem vector_map_get {α β : Type*} {d : ℕ} (f : α → β) (v : Vector α d) (i : Fin d) :
    (v.map f).get i = f (v.get i) := Vector.getElem_map f i.isLt


def ofUnreduced (a : UnreducedRational) : BinaryFraction :=
  ⟨SignedBinary.ofInt a.num, a.den.bits, by simpa only [bitWordValue_bits] using a.den_pos⟩

@[simp] theorem ofUnreduced_representation (a : UnreducedRational) :
    (ofUnreduced a).representation = a := by
  apply UnreducedRational.eq_of_num_den
  · exact SignedBinary.value_ofInt _
  · exact bitWordValue_bits _

theorem ofUnreduced_width (a : UnreducedRational) :
    (ofUnreduced a).width = max (Nat.size a.num.natAbs) (Nat.size a.den) := by
  simp only [ofUnreduced, width, SignedBinary.ofInt, ← Nat.size_eq_bits_len]




@[simp] theorem nat_representation (n : ℕ) : (nat n).representation = UnreducedRational.nat n := by
  apply UnreducedRational.eq_of_num_den
  · change (SignedBinary.ofInt (n : ℤ)).value = (n : ℤ)
    exact SignedBinary.value_ofInt _
  · rfl



theorem one_representation : one.representation = UnreducedRational.one := by
  rw [one, nat_representation]
  rfl



theorem subWithWork_representation (a b : BinaryFraction) :
    (a.subWithWork b).1.representation = a.representation.sub b.representation := by
  simp only [subWithWork, canonicalAddWithWork_representation, neg_representation,
    UnreducedRational.sub]



theorem divWithWork_representation (a b : BinaryFraction) :
    (a.divWithWork b).1.representation = a.representation.div b.representation := by
  simp only [divWithWork, canonicalMulWithWork_representation, invWithWork_representation,
    UnreducedRational.div]



theorem powWithWork_representation (a : BinaryFraction) (k : ℕ) :
    (a.powWithWork k).1.representation = a.representation.pow k := by
  induction k with
  | zero => exact one_representation
  | succ k ih => simp only [powWithWork, canonicalMulWithWork_representation,
      UnreducedRational.pow, ih]



theorem logarithmPartialWithWork_representation (b : BinaryFraction) (k : ℕ) :
    (b.logarithmPartialWithWork k).1.representation = b.representation.logarithmPartial k := by
  induction k with
  | zero => exact zero_representation
  | succ k ih => simp only [logarithmPartialWithWork, canonicalAddWithWork_representation,
      divWithWork_representation, powWithWork_representation, nat_representation,
      UnreducedRational.logarithmPartial, ih]



theorem logarithmWithWork_representation (r : BinaryFraction) (k : ℕ) :
    (r.logarithmWithWork k).1.representation = r.representation.logarithm k := by
  simp only [logarithmWithWork, canonicalMulWithWork_representation,
    logarithmPartialWithWork_representation, divWithWork_representation,
    subWithWork_representation, canonicalAddWithWork_representation,
    nat_representation, one_representation, UnreducedRational.logarithm]



theorem dotListWithWork_representation {d : ℕ} (left right : Vector BinaryFraction d)
    (indices : List (Fin d)) :
    (dotListWithWork left right indices).1.representation =
      UnreducedRational.dotList (left.map representation) (right.map representation) indices := by
  induction indices with
  | nil => exact zero_representation
  | cons i rest ih =>
    simp only [dotListWithWork, canonicalAddWithWork_representation,
      canonicalMulWithWork_representation, UnreducedRational.dotList, ih, vector_map_get]



theorem dotWithWork_representation {d : ℕ} (left right : Vector BinaryFraction d) :
    (dotWithWork left right).1.representation =
      UnreducedRational.dot (left.map representation) (right.map representation) :=
  dotListWithWork_representation _ _ _



theorem gradientCellWithWork_representation {d : ℕ} (G : ℕ)
    (linear point : Vector BinaryFraction d) (i : Fin d) :
    (gradientCellWithWork G linear point i).1.representation =
      UnreducedRational.gradientCell G (linear.map representation) (point.map representation) i := by
  simp only [gradientCellWithWork, canonicalAddWithWork_representation,
    subWithWork_representation, logarithmWithWork_representation, neg_representation,
    one_representation, invWithWork_representation, powWithWork_representation,
    nat_representation, UnreducedRational.gradientCell, vector_map_get]

theorem nat_width_le_storageBits (n : ℕ) : (nat n).width ≤ (nat n).representation.storageBits := by
  rw [nat_representation]
  have hw : (nat n).width = max (Nat.size n) 1 := by
    simp only [nat, width, SignedBinary.ofInt, Int.natAbs_natCast, ← Nat.size_eq_bits_len,
      List.length_cons, List.length_nil]
  rw [hw]
  simp only [UnreducedRational.nat, UnreducedRational.storageBits, Int.natAbs_natCast, Nat.size_one]
  omega

theorem zero_width_le_storageBits : zero.width ≤ zero.representation.storageBits := by decide

theorem powWithWork_width_le_storageBits (a : BinaryFraction) (n : ℕ) :
    (a.powWithWork n).1.width ≤ (a.powWithWork n).1.representation.storageBits := by
  cases n with
  | zero => exact nat_width_le_storageBits 1
  | succ n =>
    dsimp only [powWithWork]
    exact canonicalMulWithWork_self_width (a.powWithWork n).1 a

theorem logarithmPartialWithWork_width_le_storageBits (b : BinaryFraction) (n : ℕ) :
    (b.logarithmPartialWithWork n).1.width ≤
      (b.logarithmPartialWithWork n).1.representation.storageBits := by
  cases n with
  | zero => exact zero_width_le_storageBits
  | succ n =>
    dsimp only [logarithmPartialWithWork]
    exact canonicalAddWithWork_self_width _ _

theorem logarithmWithWork_width_le_storageBits (r : BinaryFraction) (n : ℕ) :
    (r.logarithmWithWork n).1.width ≤ (r.logarithmWithWork n).1.representation.storageBits := by
  dsimp only [logarithmWithWork]
  exact canonicalMulWithWork_self_width _ _

theorem dotListWithWork_width_le_storageBits {d : ℕ} (left right : Vector BinaryFraction d)
    (indices : List (Fin d)) :
    (dotListWithWork left right indices).1.width ≤
      (dotListWithWork left right indices).1.representation.storageBits := by
  cases indices with
  | nil => exact zero_width_le_storageBits
  | cons i rest =>
    dsimp only [dotListWithWork]
    exact canonicalAddWithWork_self_width _ _

theorem gradientCellWithWork_width_le_storageBits {d : ℕ} (G : ℕ)
    (linear point : Vector BinaryFraction d) (i : Fin d) :
    (gradientCellWithWork G linear point i).1.width ≤
      (gradientCellWithWork G linear point i).1.representation.storageBits := by
  dsimp only [gradientCellWithWork]
  exact canonicalAddWithWork_self_width _ _

end BinaryFraction
end EditApproximation

end OAI
