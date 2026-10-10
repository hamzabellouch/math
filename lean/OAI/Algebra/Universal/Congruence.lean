import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Hom.Basic

namespace OAI

/-!
# Congruences of finite-signature algebras

An algebra has finitely many total operations of finite arity, including possibly nullary
operations. Its congruences are ordered by inclusion. Compatibility with every operation is
equivalent to stability under the unary translations obtained by fixing all but one input.
-/

namespace FiniteCongruence

/-- A finite list of total finite-arity operations. Arity zero is allowed. -/
structure Algebra (Carrier : Type) where
  numOps : ℕ
  arity : Fin numOps → ℕ
  op : (index : Fin numOps) → (Fin (arity index) → Carrier) → Carrier

/-- Compatibility with all operations of an algebra. -/
def Compatible {Carrier : Type} (alg : Algebra Carrier) (rel : Setoid Carrier) : Prop :=
  ∀ (index : Fin alg.numOps) (left right : Fin (alg.arity index) → Carrier),
    (∀ coord, rel (left coord) (right coord)) → rel (alg.op index left) (alg.op index right)

/-- The full ordered set of congruences, ordered by inclusion of relations. -/
def Congruence {Carrier : Type} (alg : Algebra Carrier) :=
  {rel : Setoid Carrier // Compatible alg rel}

instance {Carrier : Type} (alg : Algebra Carrier) : PartialOrder (Congruence alg) :=
  inferInstanceAs (PartialOrder {rel : Setoid Carrier // Compatible alg rel})

/-- Order-isomorphism with the entire congruence lattice of a nonempty finite algebra. -/
def Representable (Lat : Type) [PartialOrder Lat] : Prop :=
  ∃ size : ℕ, 0 < size ∧ ∃ alg : Algebra (Fin size), Nonempty (Lat ≃o Congruence alg)

instance {Carrier : Type} {alg : Algebra Carrier} :
    CoeFun (Congruence alg) (fun _ => Carrier → Carrier → Prop) :=
  ⟨fun rel => rel.1⟩

namespace Congruence

variable {Carrier : Type} {alg : Algebra Carrier}

@[ext] theorem ext {rel other : Congruence alg}
    (equal : ∀ left right, rel left right ↔ other left right) : rel = other :=
  Subtype.ext (Setoid.ext equal)

theorem refl (rel : Congruence alg) (point : Carrier) : rel point point := rel.1.refl' point

theorem symm (rel : Congruence alg) {left right : Carrier} (related : rel left right) :
    rel right left := rel.1.symm' related

theorem trans (rel : Congruence alg) {left middle right : Carrier}
    (first : rel left middle) (second : rel middle right) : rel left right :=
  rel.1.trans' first second

theorem compatible (rel : Congruence alg) (index : Fin alg.numOps)
    (left right : Fin (alg.arity index) → Carrier) (related : ∀ coord, rel (left coord) (right coord)) :
    rel (alg.op index left) (alg.op index right) := rel.2 index left right related

/-- Equality is the least congruence. -/
def equality (alg : Algebra Carrier) : Congruence alg :=
  ⟨⊥, by
    intro index left right related
    have : left = right := funext related
    subst right
    rfl⟩

@[simp] theorem equality_apply (left right : Carrier) :
    equality alg left right ↔ left = right := Iff.rfl

theorem equality_le (rel : Congruence alg) : equality alg ≤ rel := by
  intro left right equal
  cases equal
  exact rel.refl left

/-- The intersection of all congruences containing the generating pair. -/
def principal (alg : Algebra Carrier) (left right : Carrier) : Congruence alg :=
  ⟨⟨fun first second => ∀ rel : Congruence alg, rel left right → rel first second,
     ⟨fun point rel _ => rel.refl point,
       fun related rel contains => rel.symm (related rel contains),
       fun first second rel contains => rel.trans (first rel contains) (second rel contains)⟩⟩,
   by
    intro index first second related rel contains
    exact rel.compatible index first second (fun coord => related coord rel contains)⟩

theorem principal_pair (left right : Carrier) : principal alg left right left right :=
  fun _ related => related

theorem principal_le {left right : Carrier} {rel : Congruence alg} :
    principal alg left right ≤ rel ↔ rel left right := by
  constructor
  · intro below
    exact below (principal_pair left right)
  · intro contains first second related
    exact related rel contains

theorem principal_comm (left right : Carrier) :
    principal alg left right = principal alg right left := by
  apply le_antisymm
  · exact principal_le.mpr ((principal alg right left).symm (principal_pair right left))
  · exact principal_le.mpr ((principal alg left right).symm (principal_pair left right))

end Congruence

/-- Stability under all single-coordinate changes entails compatibility with a total operation.
For nullary operations the two input tuples are equal. -/
theorem relation_map_of_updates {Carrier : Type} (rel : Setoid Carrier) {arity : ℕ}
    (operation : (Fin arity → Carrier) → Carrier)
    (stable : ∀ (coord : Fin arity) (inputs : Fin arity → Carrier) (left right : Carrier),
      rel left right →
      rel (operation (Function.update inputs coord left))
        (operation (Function.update inputs coord right)))
    (left right : Fin arity → Carrier) (related : ∀ coord, rel (left coord) (right coord)) :
    rel (operation left) (operation right) := by
  induction arity with
  | zero =>
    have : left = right := Subsingleton.elim _ _
    simp [this]
  | succ arity inductionHyp =>
    have headStep : rel (operation (Fin.cons (left 0) (Fin.tail left)))
        (operation (Fin.cons (right 0) (Fin.tail left))) := by
      simpa only [Fin.update_cons_zero] using
        stable 0 (Fin.cons (left 0) (Fin.tail left)) (left 0) (right 0) (related 0)
    have tailStep : rel (operation (Fin.cons (right 0) (Fin.tail left)))
        (operation (Fin.cons (right 0) (Fin.tail right))) := by
      apply inductionHyp (fun inputs => operation (Fin.cons (right 0) inputs))
          (fun coord inputs first second pairRelated => ?_) (Fin.tail left) (Fin.tail right)
          (fun coord => related coord.succ)
      simpa only [Fin.cons_update] using
        stable coord.succ (Fin.cons (right 0) inputs) first second pairRelated
    simpa only [Fin.cons_self_tail] using rel.trans' headStep tailStep

/-- A one-variable translation is obtained by fixing all but one input of an operation. -/
def translation {Carrier : Type} (alg : Algebra Carrier) (index : Fin alg.numOps)
    (coord : Fin (alg.arity index)) (inputs : Fin (alg.arity index) → Carrier)
    (point : Carrier) : Carrier :=
  alg.op index (Function.update inputs coord point)

theorem translation_preserves {Carrier : Type} {alg : Algebra Carrier} (rel : Congruence alg)
    (index : Fin alg.numOps) (coord : Fin (alg.arity index))
    (inputs : Fin (alg.arity index) → Carrier) {left right : Carrier} (related : rel left right) :
    rel (translation alg index coord inputs left) (translation alg index coord inputs right) := by
  apply rel.compatible
  intro other
  by_cases equal : other = coord
  · subst other
    simpa only [Function.update_self] using related
  · simpa only [Function.update_of_ne equal] using rel.refl (inputs other)

theorem compatible_iff_translations {Carrier : Type} (alg : Algebra Carrier)
    (rel : Setoid Carrier) :
    Compatible alg rel ↔ ∀ (index : Fin alg.numOps) (coord : Fin (alg.arity index))
      (inputs : Fin (alg.arity index) → Carrier) (left right : Carrier), rel left right →
      rel (translation alg index coord inputs left) (translation alg index coord inputs right) := by
  constructor
  · intro compatible index coord inputs left right related
    exact translation_preserves ⟨rel, compatible⟩ index coord inputs related
  · intro stable index left right related
    exact relation_map_of_updates rel (alg.op index) (stable index) left right related

end FiniteCongruence

end OAI
