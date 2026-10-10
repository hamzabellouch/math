import Mathlib
import OAI.GroupTheory.SimpleOvergroups.BoundedForms
import OAI.GroupTheory.SimpleOvergroups.SemanticEnlargements

namespace OAI


noncomputable section
open scoped Classical
namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding EffectiveNames NamedAction SourceEnlargement
namespace SemanticDouble

local instance : Primcodable (ZMod 2) := FiniteAlgebraicEnvelopes.Effect.finitePrimcodable _
local instance : Primcodable (ZMod 3) := FiniteAlgebraicEnvelopes.Effect.finitePrimcodable _

theorem orbit_step {V Y : Type} [Group V] [MulAction V Y]
    (w : Double.W V) (v : Double.W₁ V) (y : Y) :
    (w * groupEmbedding (ZMod 3) v) • Double.ambientPoint y =
      w • pointEmbedding (ZMod 3) (v • pointEmbedding (ZMod 2) y) := by
  rw [mul_smul]
  exact congrArg (fun x => w • x) (groupEmbedding_pointEmbedding (ZMod 3) v _)

theorem orbit_surjective {V Y U B P : Type} [Group V] [MulAction V Y]
    (f : U → Double.W V) (t : B → Y) (p : P → Double.Y (Q:=V) (X:=Y))
    (b : U → B → P) (hp : ∀ u x, (p (b u x)).val = f u • Double.ambientPoint (t x))
    (hf : Function.Surjective f) (ht : Function.Surjective t) : Function.Surjective p := by
  intro y
  obtain ⟨w,x,h⟩ := y.property
  obtain ⟨u,hu⟩ := hf w
  obtain ⟨a,ha⟩ := ht x
  refine ⟨b u a,Subtype.ext ?_⟩
  exact (hp u a).trans ((congrArg₂ (fun (w : Double.W V) (x : Double.AmbientY Y) => w • x)
      hu (congrArg Double.ambientPoint ha)).trans h)

variable {G X V Y K L : Type} [Group V] [MulAction V Y] [Nonempty Y]
  [Primcodable K] [Primcodable L] {m : ℕ}
  (N : Operations G X) (C : ActionCalculus V Y K L m) (I : Interpretation N C)

abbrev P₁ := IdempotentNames.Index (ZMod 2)
abbrev P₂ := IdempotentNames.Index (ZMod 3)
abbrev N₁ := Enlargement.operations (P:=P₁) N
abbrev N₂ := Enlargement.operations (P:=P₂) (N₁ N)
abbrev C₁ := SemanticEnlargement.calculus (k:=ZMod 2) C
abbrev I₁ := SemanticEnlargement.interpretation (k:=ZMod 2) N C I
abbrev C₂ := SemanticEnlargement.calculus (k:=ZMod 3) (C₁ C)
abbrev I₂ := SemanticEnlargement.interpretation (k:=ZMod 3) (N₁ N) (C₁ C) (I₁ N C I)

abbrev GroupName := Enlargement.Word P₂ (Enlargement.Word P₁ G)
abbrev PointName := Enlargement.Point P₂ (Enlargement.Word P₁ G) (Enlargement.Point P₁ G X)

 theorem point_in_orbit (x : PointName (G:=G) (X:=X)) :
    (I₂ N C I |>.point x).val ∈ Double.orbitSet (Q:=V) (X:=Y) := by
  refine ⟨(I₂ N C I |>.group x.1).val *
    groupEmbedding (ZMod 3) (I₁ N C I |>.group x.2.1).val, (I.point x.2.2).val, ?_⟩
  exact orbit_step _ _ _

def calculus : ActionCalculus (Double.W V) (Double.Y (Q:=V) (X:=Y)) (ℕ × ℕ) ℕ m where
  group := (C₂ C).group
  point :=
    { ball := fun b y => (C₂ C).point.ball b y.val
      mono := fun _ _ h _ hy => (C₂ C).point.mono h hy
      key := fun y => (C₂ C).point.key y.val }
  one_mem := (C₂ C).one_mem
  inv_mem := (C₂ C).inv_mem
  mul_mem := (C₂ C).mul_mem
  smul_mem := (C₂ C).smul_mem
  inv_congr := (C₂ C).inv_congr
  mul_congr := (C₂ C).mul_congr
  smul_congr := (C₂ C).smul_congr

def interpretation : Interpretation (N₂ N) (calculus C) where
  group := (I₂ N C I).group
  point x := ⟨⟨(I₂ N C I |>.point x).val,point_in_orbit N C I x⟩,
    (I₂ N C I |>.point x).cost, (I₂ N C I |>.point x).mem⟩
  group_cost := (I₂ N C I).group_cost
  point_cost := (I₂ N C I).point_cost
  one := (I₂ N C I).one
  mul := (I₂ N C I).mul
  inv := (I₂ N C I).inv
  act g x := WithBound.ext'
    (Subtype.ext (congrArg WithBound.val ((I₂ N C I).act g x)))
    (congrArg (fun t : WithBound (C₂ C).point => t.cost) ((I₂ N C I).act g x))

 theorem groupKey_injective (hg : Function.Injective C.group.key) :
    Function.Injective (calculus C).group.key :=
  SemanticEnlargement.groupKey_injective (C₁ C)
    (SemanticEnlargement.groupKey_injective C hg)

 theorem pointKey_injective (hx : Function.Injective C.point.key) :
    Function.Injective (calculus C).point.key := by
  intro a b h
  apply Subtype.ext
  exact SemanticEnlargement.pointKey_injective (C₁ C)
    (SemanticEnlargement.pointKey_injective C hx) h

 theorem groupValue_surjective (hg : Function.Surjective (fun g => (I.group g).val)) :
    Function.Surjective (fun g => (interpretation N C I |>.group g).val) :=
  SemanticEnlargement.groupValue_surjective (N₁ N) (C₁ C) (I₁ N C I)
    (SemanticEnlargement.groupValue_surjective N C I hg)

 theorem pointValue_base (u : GroupName (G:=G)) (b : X) :
    (I₂ N C I |>.point (u,([],b))).val =
      (I₂ N C I |>.group u).val • Double.ambientPoint (I.point b).val := by
  exact congrArg (fun y => (I₂ N C I |>.group u).val • pointEmbedding (ZMod 3) y)
    (SemanticEnlargement.pointValue_basis (k:=ZMod 2) N C I b)

 theorem pointValue_surjective (hg : Function.Surjective (fun g => (I.group g).val))
    (hx : Function.Surjective (fun x => (I.point x).val)) :
    Function.Surjective (fun x => (interpretation N C I |>.point x).val) :=
  orbit_surjective (fun g => (I₂ N C I |>.group g).val) (fun x => (I.point x).val)
    (fun x => (interpretation N C I |>.point x).val) (fun u b => (u,([],b)))
    (pointValue_base N C I) (groupValue_surjective N C I hg) hx

variable [Primcodable G] [Primcodable X]
omit [Primcodable G] [Primcodable X] in
 theorem partialGroupKey_full (f : G → Part K) (w : GroupName (G:=G)) {d : ℕ}
    (hw : (N₂ N).gcost w ≤ d) (hf : ∀ g, N.gcost g ≤ d → I.gkey g ∈ f g) :
    (interpretation N C I).gkey w ∈
      Enlargement.partialGroupKey (N₁ N) (IdempotentNames.name (k:=ZMod 3))
        (Enlargement.partialGroupKey N (IdempotentNames.name (k:=ZMod 2)) f) w := by
  apply SemanticEnlargement.partialGroupKey_full (N₁ N) (C₁ C) (I₁ N C I) _ w hw
  intro v hv
  exact SemanticEnlargement.partialGroupKey_full N C I f v hv hf

omit [Primcodable G] [Primcodable X] in
 theorem partialPointKey_full (f : X → Part L) (x : PointName (G:=G) (X:=X)) {d : ℕ}
    (hx : (N₂ N).xcost x ≤ d) (hf : ∀ y, N.xcost y ≤ d → I.xkey y ∈ f y) :
    (interpretation N C I).xkey x ∈
      Enlargement.partialPointKey (N₁ N) (IdempotentNames.name (k:=ZMod 3))
        (Enlargement.partialPointKey N (IdempotentNames.name (k:=ZMod 2)) f) x := by
  apply SemanticEnlargement.partialPointKey_full (N₁ N) (C₁ C) (I₁ N C I) _ x hx
  intro y hy
  exact SemanticEnlargement.partialPointKey_full N C I f y hy hf

end SemanticDouble
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
