import Mathlib
import OAI.GroupTheory.SimpleOvergroups.EnlargementEffective
import OAI.GroupTheory.SimpleOvergroups.TwoEnlargements

namespace OAI


noncomputable section
open scoped Classical
namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding EffectiveNames NamedAction SourceEnlargement

namespace IdempotentNames
abbrev Index (k : Type) [CommRing k] := BinaryPrefixOperators.idempotents k
instance {k : Type} [CommRing k] [Finite k] : Fintype (Index k) :=
  (BinaryPrefixOperators.idempotents_finite k).fintype
instance {k : Type} [CommRing k] [Finite k] : Primcodable (Index k) :=
  FiniteAlgebraicEnvelopes.Effect.finitePrimcodable _

variable {k : Type} [CommRing k]
def name (p : Index k) : Enlargement.Coeff.Name k :=
  (BinaryPrefixOperators.Arithmetic.Lists.value_surjective p.val).choose
@[simp] theorem value_name (p : Index k) : Enlargement.Coeff.value (name p) = p.val :=
  (BinaryPrefixOperators.Arithmetic.Lists.value_surjective p.val).choose_spec
 theorem idempotent (p : Index k) :
    Enlargement.Coeff.value (name p) * Enlargement.Coeff.value (name p) =
      Enlargement.Coeff.value (name p) := by
  simpa only [value_name] using BinaryPrefixOperators.idempotents_are_idempotent k p.property
end IdempotentNames

namespace SemanticEnlargement
variable {G X V Y K L k : Type} [Group V] [MulAction V Y] [Nonempty Y]
  [CommRing k] [Primcodable k] [Primcodable K] [Primcodable L]
  {m : ℕ} (N : Operations G X) (C : ActionCalculus V Y K L m)
  (I : Interpretation N C)

local instance restrictedSMul : SMul (enlargedGroup k V) (enlargedSet k Y) :=
  (SourceEnlargement.enlargedAction k V Y).toSMul

abbrev Word := Enlargement.Word (IdempotentNames.Index k) G
abbrev Point := Enlargement.Point (IdempotentNames.Index k) G X

abbrev ambient := Enlargement.interpretation N (IdempotentNames.name (k:=k)) I IdempotentNames.idempotent

def calculus : ActionCalculus (enlargedGroup k V) (enlargedSet k Y) (ℕ × ℕ) ℕ m where
  group :=
    { ball := fun b w => (Enlargement.calculus (k:=k) C).group.ball b w.val
      mono := fun _ _ h _ hw => (Enlargement.calculus (k:=k) C).group.mono h hw
      key := fun w => (Enlargement.calculus (k:=k) C).group.key w.val }
  point := (Enlargement.calculus (k:=k) C).point
  one_mem := (Enlargement.calculus (k:=k) C).one_mem
  inv_mem := (Enlargement.calculus (k:=k) C).inv_mem
  mul_mem := (Enlargement.calculus (k:=k) C).mul_mem
  smul_mem := (Enlargement.calculus (k:=k) C).smul_mem
  inv_congr := (Enlargement.calculus (k:=k) C).inv_congr
  mul_congr := (Enlargement.calculus (k:=k) C).mul_congr
  smul_congr := (Enlargement.calculus (k:=k) C).smul_congr

omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
 theorem group_mem (w : Word (k:=k) (G:=G)) :
    Enlargement.groupValue N (IdempotentNames.name (k:=k)) I IdempotentNames.idempotent w ∈ enlargedGroup k V := by
  induction w with
  | nil => exact (enlargedGroup k V).one_mem
  | cons a w ih =>
    apply (enlargedGroup k V).mul_mem _ ih
    change SourceEnlargement.unitMap _ _ _ ∈ _
    simp only [IdempotentNames.value_name]
    exact Subgroup.subset_closure ⟨a.1, (I.group a.2).val, rfl⟩

def groupValue (w : Word (k:=k) (G:=G)) : enlargedGroup k V :=
  ⟨Enlargement.groupValue N IdempotentNames.name I IdempotentNames.idempotent w,group_mem N C I w⟩
def pointValue (x : Point (k:=k) (G:=G) (X:=X)) : enlargedSet k Y :=
  Enlargement.pointValue N IdempotentNames.name I IdempotentNames.idempotent x

omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
@[simp] theorem groupValue_nil : groupValue N C I ([] : Word (k:=k) (G:=G)) = 1 := rfl
omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
@[simp] theorem groupValue_append (u v : Word (k:=k) (G:=G)) :
    groupValue N C I (u++v) = groupValue N C I u * groupValue N C I v := by
  apply Subtype.ext
  exact Enlargement.groupValue_append _ _ _ _ _ _
omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
@[simp] theorem groupValue_inverse (u : Word (k:=k) (G:=G)) :
    groupValue N C I (Enlargement.inverse N u) = (groupValue N C I u)⁻¹ := by
  apply Subtype.ext
  exact Enlargement.groupValue_inverse _ _ _ _ _
omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
@[simp] theorem groupValue_singleton (p : IdempotentNames.Index k) (g : G) :
    groupValue N C I [(p,g)] = SourceEnlargement.j k p (I.group g).val := by
  apply Subtype.ext
  simp [groupValue,
    Enlargement.groupValue, Enlargement.rootValue, SourceEnlargement.j, SourceEnlargement.map]
  rfl

omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
@[simp] theorem pointValue_act (g : Word (k:=k) (G:=G)) (x : Point (k:=k) (G:=G) (X:=X)) :
    pointValue N C I (g++x.1,x.2) = groupValue N C I g • pointValue N C I x :=
  Enlargement.pointValue_act _ _ _ _ _ _
omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
@[simp] theorem pointValue_basis (x : X) :
    pointValue N C I (([] : Word (k:=k) (G:=G)),x) = pointEmbedding k (I.point x).val := by
  simp only [pointValue, Enlargement.pointValue, Enlargement.groupValue_nil, one_smul,
    pointEmbedding]

def interpretation : Interpretation (Enlargement.operations (P:=IdempotentNames.Index k) N)
    (calculus (k:=k) C) where
  group w := ⟨groupValue N C I w,Enlargement.gcost N w,Enlargement.group_mem N IdempotentNames.name I IdempotentNames.idempotent w⟩
  point x := ⟨pointValue N C I x, Enlargement.xcost N x,
    Enlargement.point_mem N IdempotentNames.name I IdempotentNames.idempotent x⟩
  group_cost _ := rfl
  point_cost _ := rfl
  one := WithBound.ext' (groupValue_nil N C I) rfl
  mul u v := WithBound.ext' (groupValue_append N C I u v) (Enlargement.gcost_append N u v)
  inv u := WithBound.ext' (groupValue_inverse N C I u) (Enlargement.gcost_inverse N u)
  act g x := WithBound.ext' (pointValue_act N C I g x)
    (by change Enlargement.xcost N (g++x.1,x.2) = Enlargement.gcost N g + Enlargement.xcost N x
        simp [Enlargement.xcost,Nat.add_assoc])

 theorem groupKey_injective (hg : Function.Injective C.group.key) :
    Function.Injective (calculus (k:=k) C).group.key := by
  intro u v h
  apply Subtype.ext
  apply Units.ext
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.mapDomain_injective hg
  exact congrArg Prod.fst (Enlargement.pairedKey_injective h)

 theorem pointKey_injective (hx : Function.Injective C.point.key) :
    Function.Injective (calculus (k:=k) C).point.key := by
  intro u v h
  exact Finsupp.mapDomain_injective hx (Enlargement.arrayKey_injective h)

omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
 theorem groupValue_surjective (hg : Function.Surjective (fun g => (I.group g).val)) :
    Function.Surjective (groupValue (k:=k) N C I) := by
  intro w
  have h : ∃ u, (groupValue N C I u).val = w.val := by
    apply Subgroup.closure_induction (p:=fun w _ => ∃ u, (groupValue N C I u).val = w) (hx:=w.property)
    · rintro _ ⟨p,g,rfl⟩
      obtain ⟨a,rfl⟩ := hg g
      exact ⟨[(p,a)],congrArg Subtype.val (groupValue_singleton N C I p a)⟩
    · exact ⟨[],rfl⟩
    · rintro _ _ _ _ ⟨u,rfl⟩ ⟨v,rfl⟩
      exact ⟨u++v,congrArg Subtype.val (groupValue_append N C I u v)⟩
    · rintro _ _ ⟨u,rfl⟩
      exact ⟨Enlargement.inverse N u,congrArg Subtype.val (groupValue_inverse N C I u)⟩
  obtain ⟨u,hu⟩ := h
  exact ⟨u,Subtype.ext hu⟩

variable [Primcodable G] [Primcodable X]
omit [Primcodable G] [Primcodable X] in
 theorem partialGroupKey_full (f : G → Part K) (w : Word (k:=k) (G:=G)) {d : ℕ}
    (hw : Enlargement.gcost N w ≤ d) (hf : ∀ g, N.gcost g ≤ d → I.gkey g ∈ f g) :
    (interpretation N C I).gkey w ∈ Enlargement.partialGroupKey N IdempotentNames.name f w :=
  Enlargement.partialGroupKey_full _ _ _ _ _ _ hw hf

omit [Primcodable G] [Primcodable X] in
 theorem partialPointKey_full (f : X → Part L) (x : Point (k:=k) (G:=G) (X:=X)) {d : ℕ}
    (hx : Enlargement.xcost N x ≤ d) (hf : ∀ y, N.xcost y ≤ d → I.xkey y ∈ f y) :
    (interpretation N C I).xkey x ∈ Enlargement.partialPointKey N IdempotentNames.name f x :=
  Enlargement.partialPointKey_full _ _ _ _ _ _ hx hf

end SemanticEnlargement
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
