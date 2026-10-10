import Mathlib
import OAI.GroupTheory.FiniteType.AscendingHNNInnerTwist
import OAI.GroupTheory.FiniteType.BinaryPrefixOperators
import OAI.GroupTheory.FiniteType.TwistedBrinGermBrick
import OAI.GroupTheory.SimpleOvergroups.EnlargementCore

namespace OAI

noncomputable section
namespace SourceEnlargement

section OneLayer
variable (K : Type) [CommRing K]
variable (V Z : Type) [Group V] [MulAction V Z]

abbrev enlargedGroup := group (V := V) (BinaryPrefixOperators.idempotents K)
  (fun _ h => BinaryPrefixOperators.idempotents_are_idempotent K h)

abbrev enlargedSet := Z →₀ BinaryPrefixOperators.algebra K

instance enlargedAction : MulAction (enlargedGroup K V) (enlargedSet K Z) :=
  @MulAction.compHom _ _ _ _
    (unitsAction (D := BinaryPrefixOperators.algebra K) (V := V) (Z := Z))
    _ (enlargedGroup K V).subtype

variable {V Z}

def j (E : BinaryPrefixOperators.idempotents K) : V →* enlargedGroup K V :=
  map (BinaryPrefixOperators.idempotents K)
    (fun _ h => BinaryPrefixOperators.idempotents_are_idempotent K h) E

def groupEmbedding : V →* enlargedGroup K V :=
  j K ⟨1, BinaryPrefixOperators.identity_mem K⟩

def pointEmbedding (z : Z) : enlargedSet K Z := Finsupp.single z 1

lemma groupEmbedding_injective [Nontrivial K] :
    Function.Injective (groupEmbedding (V := V) K) :=
  map_identity_injective (BinaryPrefixOperators.idempotents K)
    (fun _ h => BinaryPrefixOperators.idempotents_are_idempotent K h)
    (BinaryPrefixOperators.identity_mem K)

lemma pointEmbedding_injective [Nontrivial K] :
    Function.Injective (pointEmbedding (Z := Z) K) := basis_injective

lemma groupEmbedding_pointEmbedding (g : V) (z : Z) :
    groupEmbedding K g • pointEmbedding K z = pointEmbedding K (g • z) :=
  map_identity_basis (BinaryPrefixOperators.idempotents K)
    (fun _ h => BinaryPrefixOperators.idempotents_are_idempotent K h)
    (BinaryPrefixOperators.identity_mem K) g z

def pairDiagrams : StageGeometry.PairDiagrams K
    (groupEmbedding (V := V) K) (pointEmbedding (Z := Z) K) where
  map := j K
  identity := rfl
  commute E P _hSum hEP hPE g h :=
    map_commute _ _ E P hEP hPE g h
  addition E P hSum hEP _hPE g := map_add _ _ E P hSum hEP g
  fixed E g z hz := map_fixes _ _ E g z hz

end OneLayer

def diagramsForward {Q W W' X Y Y' : Type} [Group Q] [Group W] [Group W']
    [MulAction Q X] [MulAction W Y] [MulAction W' Y']
    {K : Type} [CommRing K] {i : Q →* W} {t : X → Y}
    (D : StageGeometry.PairDiagrams K i t)
    (f : W →* W') (a : Y → Y') (h : ∀ w y, f w • a y = a (w • y)) :
    StageGeometry.PairDiagrams K (f.comp i) (a ∘ t) where
  map E := f.comp (D.map E)
  identity := congrArg (f.comp) D.identity
  commute E P hsum hEP hPE q u := (D.commute E P hsum hEP hPE q u).map f
  addition E P hsum hEP hPE q := by
    change f (D.map ⟨E.val + P.val, hsum⟩ q) = f (D.map E q) * f (D.map P q)
    rw [D.addition E P hsum hEP hPE, map_mul]
  fixed E q x hx := by
    change f (D.map E q) • a (t x) = a (t x)
    rw [h, D.fixed E q x hx]

def diagramsBackward {Q' Q W X' X Y : Type} [Group Q'] [Group Q] [Group W]
    [MulAction Q' X'] [MulAction Q X] [MulAction W Y]
    {K : Type} [CommRing K] {i : Q →* W} {t : X → Y}
    (D : StageGeometry.PairDiagrams K i t)
    (f : Q' →* Q) (a : X' → X) (h : ∀ q x, f q • a x = a (q • x)) :
    StageGeometry.PairDiagrams K (i.comp f) (t ∘ a) where
  map E := (D.map E).comp f
  identity := congrArg (fun j => j.comp f) D.identity
  commute E P hsum hEP hPE q u := D.commute E P hsum hEP hPE (f q) (f u)
  addition E P hsum hEP hPE q := D.addition E P hsum hEP hPE (f q)
  fixed E q x hx := D.fixed E (f q) (a x) (by rw [h, hx])

namespace Saturation
variable {W X Y : Type} [Group W] [MulAction W Y] (t : X → Y)

def carrier : Set Y := {y | ∃ (w : W) (x : X), w • t x = y}

instance action : MulAction W (carrier (W := W) t) where
  smul w y := ⟨w • y.val, by
    obtain ⟨v, x, hx⟩ := y.property
    exact ⟨w * v, x, by rw [mul_smul, hx]⟩⟩
  one_smul y := Subtype.ext (one_smul _ _)
  mul_smul w v y := Subtype.ext (mul_smul _ _ _)

def point (x : X) : carrier (W := W) t := ⟨t x, 1, x, one_smul W (t x)⟩

lemma point_injective (ht : Function.Injective t) :
    Function.Injective (point (W := W) t) := fun _ _ e => ht (congrArg Subtype.val e)

lemma equivariant {Q : Type} [Group Q] [MulAction Q X] (i : Q →* W)
    (h : ∀ q x, i q • t x = t (q • x)) (q : Q) (x : X) :
    i q • point (W := W) t x = point t (q • x) := Subtype.ext (h q x)

def diagrams {Q : Type} [Group Q] [MulAction Q X]
    {K : Type} [CommRing K] {i : Q →* W} (D : StageGeometry.PairDiagrams K i t) :
    StageGeometry.PairDiagrams K i (point (W := W) t) where
  map := D.map
  identity := D.identity
  commute := D.commute
  addition := D.addition
  fixed E q x hx := Subtype.ext (D.fixed E q x hx)
end Saturation

namespace Double
variable (Q X : Type) [Group Q] [MulAction Q X]

abbrev W₁ := enlargedGroup (ZMod 2) Q
abbrev Y₁ := enlargedSet (ZMod 2) X
abbrev W := enlargedGroup (ZMod 3) (W₁ Q)
abbrev AmbientY := enlargedSet (ZMod 3) (Y₁ X)

instance action₁ : MulAction (W₁ Q) (Y₁ X) :=
  enlargedAction (ZMod 2) Q X

instance action₂ : MulAction (W Q) (AmbientY X) :=
  enlargedAction (ZMod 3) (W₁ Q) (Y₁ X)

instance smul₁ : SMul (W₁ Q) (Y₁ X) := (action₁ Q X).toSMul
instance smul₂ : SMul (W Q) (AmbientY X) := (action₂ Q X).toSMul

variable {Q X}

def iota : Q →* W Q :=
  (groupEmbedding (ZMod 3)).comp (groupEmbedding (ZMod 2))

def ambientPoint (x : X) : AmbientY X :=
  pointEmbedding (ZMod 3) (pointEmbedding (ZMod 2) x)

lemma iota_injective : Function.Injective (iota (Q := Q)) :=
  (groupEmbedding_injective (ZMod 3)).comp (groupEmbedding_injective (ZMod 2))

lemma ambientPoint_injective : Function.Injective (ambientPoint (X := X)) :=
  (pointEmbedding_injective (ZMod 3)).comp (pointEmbedding_injective (ZMod 2))

lemma iota_ambientPoint (q : Q) (x : X) :
    (iota q • ambientPoint x : AmbientY X) = ambientPoint (q • x) := by
  change (groupEmbedding (ZMod 3) (groupEmbedding (ZMod 2) q) •
    pointEmbedding (ZMod 3) (pointEmbedding (ZMod 2) x) : AmbientY X) = _
  rw [groupEmbedding_pointEmbedding, groupEmbedding_pointEmbedding]
  rfl

def ambientDiagrams₂ : StageGeometry.PairDiagrams (ZMod 2)
    (iota (Q := Q)) (ambientPoint (X := X)) :=
  diagramsForward (pairDiagrams (V := Q) (Z := X) (ZMod 2))
    (groupEmbedding (ZMod 3)) (pointEmbedding (ZMod 3))
    (groupEmbedding_pointEmbedding (ZMod 3))

def ambientDiagrams₃ : StageGeometry.PairDiagrams (ZMod 3)
    (iota (Q := Q)) (ambientPoint (X := X)) :=
  diagramsBackward (pairDiagrams (V := W₁ Q) (Z := Y₁ X) (ZMod 3))
    (groupEmbedding (ZMod 2)) (pointEmbedding (ZMod 2))
    (groupEmbedding_pointEmbedding (ZMod 2))

def orbitSet : Set (AmbientY X) :=
  Saturation.carrier (W := W Q) (ambientPoint (X := X))

abbrev Y := orbitSet (Q := Q) (X := X)

instance orbitAction : MulAction (W Q) (Y (Q := Q) (X := X)) :=
  Saturation.action (W := W Q) (ambientPoint (X := X))

instance orbitSMul : SMul (W Q) (Y (Q := Q) (X := X)) :=
  (orbitAction (Q := Q) (X := X)).toSMul

def point (x : X) : Y (Q := Q) (X := X) :=
  Saturation.point (W := W Q) (ambientPoint (X := X)) x

lemma point_injective : Function.Injective (point (Q := Q) (X := X)) :=
  Saturation.point_injective _ ambientPoint_injective

lemma iota_point (q : Q) (x : X) :
    iota q • point (Q := Q) x = point (Q := Q) (q • x) :=
  Saturation.equivariant _ _ iota_ambientPoint q x

def diagrams₂ : StageGeometry.PairDiagrams (ZMod 2)
    (iota (Q := Q)) (point (Q := Q) (X := X)) :=
  Saturation.diagrams _ ambientDiagrams₂

def diagrams₃ : StageGeometry.PairDiagrams (ZMod 3)
    (iota (Q := Q)) (point (Q := Q) (X := X)) :=
  Saturation.diagrams _ ambientDiagrams₃

end Double
end SourceEnlargement
end

end OAI
