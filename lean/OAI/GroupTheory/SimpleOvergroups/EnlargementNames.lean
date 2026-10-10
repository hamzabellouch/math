import Mathlib
import OAI.GroupTheory.SimpleOvergroups.ArrayOperations
import OAI.GroupTheory.SimpleOvergroups.NamedActions
import OAI.GroupTheory.SimpleOvergroups.PrefixNames
import OAI.GroupTheory.SimpleOvergroups.TruncatedArrays

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Enlargement
open BoundedEncoding NamedAction
noncomputable section
namespace Coeff
open BinaryPrefixOperators.Arithmetic
abbrev Name (k : Type*) := Lists.Poly k
variable {k : Type*} [CommRing k]
abbrev value := Lists.value (K:=k)
abbrev one := Lists.oneName (K:=k)
abbrev mul := Lists.product (K:=k)
def complement (a : Name k) : Name k := one ++ Lists.negate a
@[simp] theorem value_one : value (one (k:=k)) = 1 := Lists.value_oneName
@[simp] theorem value_mul (a b : Name k) : value (mul a b) = value a * value b := Lists.value_product a b
@[simp] theorem value_complement (a : Name k) : value (complement a) = 1-value a := by
  simp [complement,sub_eq_add_neg]
end Coeff
open scoped Classical
variable {G X P k : Type*} [CommRing k] (N : Operations G X)

abbrev Word (P G : Type*) := List (P × G)
abbrev Point (P G X : Type*) := Word P G × X

def rootInv (a : P × G) : P × G := (a.1,N.inv a.2)
def inverse (w : Word P G) : Word P G := w.reverse.map (rootInv N)
def gcost (w : Word P G) : ℕ := (w.map fun a => N.gcost a.2).sum
def xcost (x : Point P G X) : ℕ := gcost N x.1 + N.xcost x.2
@[simp] theorem inverse_nil : inverse N ([] : Word P G) = [] := rfl
@[simp] theorem inverse_cons (a : P × G) (w : Word P G) :
    inverse N (a::w) = inverse N w ++ [rootInv N a] := by simp [inverse]
@[simp] theorem gcost_nil : gcost N ([] : Word P G) = 0 := rfl
@[simp] theorem gcost_cons (a : P × G) (w : Word P G) :
    gcost N (a::w) = N.gcost a.2 + gcost N w := rfl
@[simp] theorem gcost_append (u v : Word P G) : gcost N (u++v) = gcost N u + gcost N v := by simp [gcost]
@[simp] theorem gcost_inverse (w : Word P G) : gcost N (inverse N w) = gcost N w := by
  simp [gcost,inverse,List.map_map,Function.comp_def,rootInv,N.cost_inv]

def operations : Operations (Word P G) (Point P G X) where
  one := []
  mul := (·++·)
  inv := inverse N
  act w x := (w++x.1,x.2)
  gcost := gcost N
  xcost := xcost N
  cost_one := rfl
  cost_mul := gcost_append N
  cost_inv := gcost_inverse N
  cost_act := by intros; simp [xcost,Nat.add_assoc]

variable (e : P → Coeff.Name k)

def rootArray (a : P × G) : Array.Name (Coeff.Name k) G :=
  [(Coeff.complement (e a.1),N.one),(e a.1,a.2)]

def array (w : Word P G) : Array.Name (Coeff.Name k) G :=
  w.foldr (fun a p => Array.product Coeff.mul N.mul (rootArray N e a) p) [(Coeff.one,N.one)]

def pointArray (x : Point P G X) : Array.Name (Coeff.Name k) X :=
  Array.product Coeff.mul N.act (array N e x.1) [(Coeff.one,x.2)]

 theorem rootArray_bound (a : P × G) : ∀ b ∈ rootArray N e a, N.gcost b.2 ≤ N.gcost a.2 := by
  intro b hb
  simp only [rootArray,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl
  · simp [N.cost_one]
  · exact le_rfl

 theorem array_bound (w : Word P G) : ∀ b ∈ array N e w, N.gcost b.2 ≤ gcost N w := by
  induction w with
  | nil => intro b hb; simp only [array,List.foldr_nil,List.mem_singleton] at hb
           simp [hb,N.cost_one]
  | cons a w ih =>
    exact Array.product_bound Coeff.mul N.mul N.gcost N.gcost N.cost_mul
      (rootArray_bound N e a) ih

 theorem pointArray_bound (x : Point P G X) : ∀ b ∈ pointArray N e x, N.xcost b.2 ≤ xcost N x := by
  apply Array.product_bound Coeff.mul N.act N.gcost N.xcost N.cost_act (array_bound N e x.1)
  intro b hb
  simp only [List.mem_singleton] at hb
  simp [hb]

variable {V Y K L : Type*} [Group V] [MulAction V Y] [Nonempty Y] {m : ℕ}
  {C : ActionCalculus V Y K L m} (I : Interpretation N C)
  (he : ∀ p, Coeff.value (e p) * Coeff.value (e p) = Coeff.value (e p))

abbrev D (k : Type*) [CommRing k] := BinaryPrefixOperators.algebra k

def rootValue (a : P × G) : (MonoidAlgebra (D k) V)ˣ :=
  SourceEnlargement.unitMap (Coeff.value (e a.1)) (he a.1) (I.group a.2).val

def groupValue (w : Word P G) : (MonoidAlgebra (D k) V)ˣ := (w.map (rootValue N e I he)).prod

omit [Nonempty Y] in
@[simp] theorem groupValue_nil : groupValue N e I he [] = 1 := rfl
omit [Nonempty Y] in
@[simp] theorem groupValue_cons (a : P × G) (w : Word P G) :
    groupValue N e I he (a::w) = rootValue N e I he a * groupValue N e I he w := rfl
omit [Nonempty Y] in
@[simp] theorem groupValue_append (a b : Word P G) :
    groupValue N e I he (a++b) = groupValue N e I he a * groupValue N e I he b := by simp [groupValue]

omit [Nonempty Y] in
@[simp] theorem rootValue_inv (a : P × G) :
    rootValue N e I he (rootInv N a) = (rootValue N e I he a)⁻¹ := by
  simp only [rootValue,rootInv,I.inv]
  exact map_inv _ _

omit [Nonempty Y] in
@[simp] theorem groupValue_inverse (w : Word P G) :
    groupValue N e I he (inverse N w) = (groupValue N e I he w)⁻¹ := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih,mul_inv_rev]

def pointValue (x : Point P G X) : Y →₀ D k :=
  groupValue N e I he x.1 • Finsupp.single (I.point x.2).val 1

omit [Nonempty Y] in
@[simp] theorem pointValue_act (w : Word P G) (x : Point P G X) :
    pointValue N e I he (w++x.1,x.2) =
      @SMul.smul _ _ SourceEnlargement.unitsAction.toSMul (groupValue N e I he w) (pointValue N e I he x) := by
  simp only [pointValue,groupValue_append,mul_smul]
  rfl

omit [Nonempty Y] in
@[simp] theorem value_rootArray (a : P × G) :
    Array.algebraValue Coeff.value (fun g => (I.group g).val) (rootArray N e a) =
      (rootValue N e I he a).val := by
  simp only [rootArray,Array.algebraValue_cons,Array.algebraValue_nil,add_zero,Coeff.value_complement,I.one]
  rfl

omit [Nonempty Y] in
@[simp] theorem value_array (w : Word P G) :
    Array.algebraValue Coeff.value (fun g => (I.group g).val) (array N e w) =
      (groupValue N e I he w).val := by
  induction w with
  | nil => simp only [array,List.foldr_nil,Array.algebraValue_cons,Array.algebraValue_nil,add_zero,
      I.one,Coeff.value_one]; rfl
  | cons a w ih =>
    change Array.algebraValue _ _ (Array.product Coeff.mul N.mul (rootArray N e a) (array N e w)) = _
    rw [Array.algebraValue_product _ _ _ _ Coeff.value_mul (fun g h => congrArg WithBound.val (I.mul g h)),
      value_rootArray N e I he,ih]
    rfl

omit [Nonempty Y] in
@[simp] theorem value_pointArray (x : Point P G X) :
    Array.value Coeff.value (fun x => (I.point x).val) (pointArray N e x) = pointValue N e I he x := by
  unfold pointArray
  rw [Array.value_action _ _ _ _ _ Coeff.value_mul (fun g x => congrArg WithBound.val (I.act g x)),
    value_array N e I he]
  simp only [Array.value_cons,Array.value_nil,add_zero,Coeff.value_one]
  rfl

 theorem group_mem (w : Word P G) :
    groupValue N e I he w ∈ (C.enlargement (D k)).group.ball (gcost N w) := by
  induction w with
  | nil => exact (C.enlargement (D k)).one_mem _
  | cons a w ih =>
    apply (C.enlargement (D k)).mul_mem _ ih
    have hh := C.unitMap_mem (D k) (Coeff.value (e a.1)) (he a.1) (I.group a.2).mem
    simpa only [I.group_cost,rootValue] using hh

 theorem point_mem (x : Point P G X) :
    pointValue N e I he x ∈ (C.enlargement (D k)).point.ball (xcost N x) := by
  apply (C.enlargement (D k)).smul_mem (group_mem N e I he x.1)
  have hh := C.basis_mem (D k) (I.point x.2).mem
  simpa only [I.point_cost] using hh

end
end SimpleFInftyOvergroups.EffectiveNames.Enlargement

end OAI
