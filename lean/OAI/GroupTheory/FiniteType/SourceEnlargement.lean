import Mathlib
import OAI.GroupTheory.FiniteType.AscendingHNNInnerTwist
import OAI.GroupTheory.FiniteType.IdempotentEnlargement
import OAI.GroupTheory.FiniteType.StageGeometryProperties

namespace OAI

noncomputable section
namespace SourceEnlargement

def D₂ : Type := BinaryPrefixOperators.algebra (ZMod 2)
def D₃ : Type := BinaryPrefixOperators.algebra (ZMod 3)
instance : Ring D₂ := inferInstanceAs (Ring (BinaryPrefixOperators.algebra (ZMod 2)))
instance : Ring D₃ := inferInstanceAs (Ring (BinaryPrefixOperators.algebra (ZMod 3)))
instance : Algebra (ZMod 2) D₂ :=
  inferInstanceAs (Algebra (ZMod 2) (BinaryPrefixOperators.algebra (ZMod 2)))
instance : Algebra (ZMod 3) D₃ :=
  inferInstanceAs (Algebra (ZMod 3) (BinaryPrefixOperators.algebra (ZMod 3)))
instance : Nontrivial D₂ :=
  inferInstanceAs (Nontrivial (BinaryPrefixOperators.algebra (ZMod 2)))
instance : Nontrivial D₃ :=
  inferInstanceAs (Nontrivial (BinaryPrefixOperators.algebra (ZMod 3)))
def P₂ : Set D₂ := BinaryPrefixOperators.idempotents (ZMod 2)
def P₃ : Set D₃ := BinaryPrefixOperators.idempotents (ZMod 3)

lemma idempotent₂ (E : D₂) (h : E ∈ P₂) : IsIdempotentElem E :=
  BinaryPrefixOperators.idempotents_are_idempotent (ZMod 2) h
lemma idempotent₃ (E : D₃) (h : E ∈ P₃) : IsIdempotentElem E :=
  BinaryPrefixOperators.idempotents_are_idempotent (ZMod 3) h

def I₂ : P₂ := ⟨1, BinaryPrefixOperators.identity_mem (ZMod 2)⟩
def I₃ : P₃ := ⟨1, BinaryPrefixOperators.identity_mem (ZMod 3)⟩

def W₁ (V : Type) [Group V] : Type :=
  IdempotentEnlargement.W (ZMod 2) D₂ V P₂ idempotent₂
instance (V : Type) [Group V] : Group (W₁ V) :=
  inferInstanceAs (Group (IdempotentEnlargement.W (ZMod 2) D₂ V P₂ idempotent₂))
def Y₁ (Z : Type) : Type := IdempotentEnlargement.ArraySpace D₂ Z
def W (V : Type) [Group V] : Type :=
  IdempotentEnlargement.W (ZMod 3) D₃ (W₁ V) P₃ idempotent₃
instance (V : Type) [Group V] : Group (W V) :=
  inferInstanceAs (Group (IdempotentEnlargement.W (ZMod 3) D₃ (W₁ V) P₃ idempotent₃))
def Y₂ (Z : Type) : Type := IdempotentEnlargement.ArraySpace D₃ (Y₁ Z)

instance layer₁Action (V Z : Type) [Group V] [MulAction V Z] :
    MulAction (W₁ V) (Y₁ Z) :=
  IdempotentEnlargement.arrayAction (ZMod 2) D₂ V Z P₂ idempotent₂

instance layer₂Action (V Z : Type) [Group V] [MulAction V Z] :
    MulAction (W V) (Y₂ Z) :=
  IdempotentEnlargement.arrayAction (ZMod 3) D₃ (W₁ V) (Y₁ Z) P₃ idempotent₃

abbrev j₂ (V : Type) [Group V] (E : P₂) : V →* W₁ V :=
  IdempotentEnlargement.j (ZMod 2) D₂ V P₂ idempotent₂ E
abbrev j₃ (V : Type) [Group V] (F : P₃) : W₁ V →* W V :=
  IdempotentEnlargement.j (ZMod 3) D₃ (W₁ V) P₃ idempotent₃ F

def iota (V : Type) [Group V] : V →* W V := (j₃ V I₃).comp (j₂ V I₂)

def point₁ (Z : Type) : Z → Y₁ Z := IdempotentEnlargement.point D₂ Z
                                                                            
def point₂ (Z : Type) : Z → Y₂ Z :=
  IdempotentEnlargement.point D₃ (Y₁ Z) ∘ point₁ Z

def family₂ (V : Type) [Group V] (E : P₂) : V →* W V :=
  (j₃ V I₃).comp (j₂ V E)
def family₃ (V : Type) [Group V] (F : P₃) : V →* W V :=
  (j₃ V F).comp (j₂ V I₂)

variable (V Z : Type) [Group V] [MulAction V Z]

local instance layer₁Smul : SMul (W₁ V) (Y₁ Z) := (layer₁Action V Z).toSMul
local instance layer₂Smul : SMul (W V) (Y₂ Z) := (layer₂Action V Z).toSMul

lemma iota_injective : Function.Injective (iota V) :=
  (IdempotentEnlargement.j_identity_injective (ZMod 3) D₃ (W₁ V) P₃ idempotent₃ I₃.property).comp
    (IdempotentEnlargement.j_identity_injective (ZMod 2) D₂ V P₂ idempotent₂ I₂.property)

lemma point₁_injective : Function.Injective (point₁ Z) :=
  IdempotentEnlargement.point_injective D₂ Z
lemma point₂_injective : Function.Injective (point₂ Z) :=
  (IdempotentEnlargement.point_injective D₃ (Y₁ Z)).comp (point₁_injective Z)

lemma point₁_equivariant (q : V) (x : Z) :
    j₂ V I₂ q • point₁ Z x = point₁ Z (q • x) :=
  IdempotentEnlargement.j_identity_equivariant (ZMod 2) D₂ V Z P₂ idempotent₂ I₂.property q x

lemma point₂_equivariant (q : V) (x : Z) :
    iota V q • point₂ Z x = point₂ Z (q • x) := by
  exact (IdempotentEnlargement.j_identity_equivariant
    (ZMod 3) D₃ (W₁ V) (Y₁ Z) P₃ idempotent₃ I₃.property (j₂ V I₂ q) (point₁ Z x)).trans
      (congrArg (IdempotentEnlargement.point D₃ (Y₁ Z)) (point₁_equivariant V Z q x))

lemma family₂_identity : family₂ V I₂ = iota V := rfl
lemma family₃_identity : family₃ V I₃ = iota V := rfl

lemma family₂_commute (E F : P₂) (hEF : E.val * F.val = 0)
    (hFE : F.val * E.val = 0) (q r : V) :
    Commute (family₂ V E q) (family₂ V F r) :=
  (IdempotentEnlargement.j_commute (ZMod 2) D₂ V P₂ idempotent₂ E F hEF hFE q r).map
    (j₃ V I₃)

lemma family₃_commute (E F : P₃) (hEF : E.val * F.val = 0)
    (hFE : F.val * E.val = 0) (q r : V) :
    Commute (family₃ V E q) (family₃ V F r) :=
  IdempotentEnlargement.j_commute (ZMod 3) D₃ (W₁ V) P₃ idempotent₃ E F hEF hFE
    (j₂ V I₂ q) (j₂ V I₂ r)

lemma family₂_addition (E F : P₂) (hSum : E.val + F.val ∈ P₂)
    (hEF : E.val * F.val = 0) (q : V) :
    family₂ V ⟨E.val+F.val,hSum⟩ q = family₂ V E q * family₂ V F q := by
  exact (congrArg (fun w => j₃ V I₃ w)
    (IdempotentEnlargement.j_addition (ZMod 2) D₂ V P₂ idempotent₂ E F hSum hEF q)).trans
      ((j₃ V I₃).map_mul _ _)

lemma family₃_addition (E F : P₃) (hSum : E.val + F.val ∈ P₃)
    (hEF : E.val * F.val = 0) (q : V) :
    family₃ V ⟨E.val+F.val,hSum⟩ q = family₃ V E q * family₃ V F q :=
  IdempotentEnlargement.j_addition (ZMod 3) D₃ (W₁ V) P₃ idempotent₃ E F hSum hEF
    (j₂ V I₂ q)

lemma family₂_fixed (E : P₂) (q : V) (x : Z) (h : q • x = x) :
    family₂ V E q • point₂ Z x = point₂ Z x := by
  exact (IdempotentEnlargement.j_identity_equivariant
    (ZMod 3) D₃ (W₁ V) (Y₁ Z) P₃ idempotent₃ I₃.property (j₂ V E q) (point₁ Z x)).trans
      (congrArg (IdempotentEnlargement.point D₃ (Y₁ Z))
        (IdempotentEnlargement.j_fixed (ZMod 2) D₂ V Z P₂ idempotent₂ E q x h))

lemma family₃_fixed (E : P₃) (q : V) (x : Z) (h : q • x = x) :
    family₃ V E q • point₂ Z x = point₂ Z x := by
  exact IdempotentEnlargement.j_fixed (ZMod 3) D₃ (W₁ V) (Y₁ Z) P₃ idempotent₃ E
    (j₂ V I₂ q) (point₁ Z x) ((point₁_equivariant V Z q x).trans (congrArg (point₁ Z) h))

def orbitPoints : Set (Y₂ Z) := {y | ∃ w : W V, ∃ x : Z, w • point₂ Z x = y}
abbrev Y := orbitPoints V Z

instance orbitAction : MulAction (W V) (Y V Z) where
  smul w y := ⟨w • y.val, by
    obtain ⟨v,x,h⟩ := y.property
    exact ⟨w*v,x, (mul_smul w v (point₂ Z x)).trans (congrArg (fun z => w • z) h)⟩⟩
  one_smul y := Subtype.ext (one_smul (W V) y.val)
  mul_smul w v y := Subtype.ext (mul_smul w v y.val)

@[simp] lemma orbit_smul_val (w : W V) (y : Y V Z) :
    (w • y).val = w • y.val := rfl

def point (x : Z) : Y V Z := ⟨point₂ Z x, ⟨1,x,one_smul _ _⟩⟩

@[simp] lemma point_val (x : Z) : (point V Z x).val = point₂ Z x := rfl

lemma point_injective : Function.Injective (point V Z) := by
  intro x y h
  exact point₂_injective Z (congrArg Subtype.val h)

lemma point_equivariant (q : V) (x : Z) :
    iota V q • point V Z x = point V Z (q • x) := by
  apply Subtype.ext
  exact point₂_equivariant V Z q x

def diagram₂ : StageGeometry.PairDiagrams (ZMod 2) (iota V) (point V Z) where
  map := family₂ V
  identity := family₂_identity V
  commute E F _hSum hEF hFE q r := family₂_commute V E F hEF hFE q r
  addition E F hSum hEF _hFE q := family₂_addition V E F hSum hEF q
  fixed E q x h := Subtype.ext (family₂_fixed V Z E q x h)

def diagram₃ : StageGeometry.PairDiagrams (ZMod 3) (iota V) (point V Z) where
  map := family₃ V
  identity := family₃_identity V
  commute E F _hSum hEF hFE q r := family₃_commute V E F hEF hFE q r
  addition E F hSum hEF _hFE q := family₃_addition V E F hSum hEF q
  fixed E q x h := Subtype.ext (family₃_fixed V Z E q x h)

end SourceEnlargement

namespace SourceEnlargement
open StageConstruction

variable {R G : Type} [Ring R] [Nontrivial R] [Group G]
local instance : DecidableEq (Y (Q R) (X R)) := Classical.decEq _

theorem overgroup_of_corner_data
    (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (e : R) (he : IsIdempotentElem e) (hne : e ≠ 0)
    (S T : Y (Q R) (X R) → he.Corner)
    (hTS : ∀ y z, T y * S z = if y = z then 1 else 0)
    (ρ : W (Q R) →* he.Cornerˣ)
    (hρS : ∀ w y, (ρ w).val * S y = S (w • y))
    (hTρ : ∀ w y, T y * (ρ w).val = T (w⁻¹ • y))
    (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
    (A : Type) [Finite A] (π : FreeAlgebra (ZMod 2) A →+* R)
    (hπ : Function.Surjective π) (rel : Set (FreeAlgebra (ZMod 2) A))
    (hrel : rel.Finite) (hker : TwoSidedIdeal.ker π = TwoSidedIdeal.span rel)
    (g : G →* he.Cornerˣ) (hg : Function.Injective g) :
    ∃ (H : Type) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
      SimpleFInftyOvergroups.HasTypeFInfty H ∧
        ∃ f : G →* H, Function.Injective f := by
  exact StageGeometry.simple_geometric_overgroup_of_corner_ring_data
    φ D e he hne S T hTS ρ (iota (Q R)) (point (Q R) (X R))
    hρS hTρ (point_equivariant (Q R) (X R)) hφ hρ (iota_injective (Q R))
    (point_injective (Q R) (X R)) (diagram₂ (Q R) (X R)) (diagram₃ (Q R) (X R))
    A π hπ rel hrel hker g hg

end SourceEnlargement

end

end OAI
