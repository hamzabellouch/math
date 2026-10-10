import Mathlib
import OAI.GroupTheory.SimpleOvergroups.DoubleEffective
import OAI.GroupTheory.SimpleOvergroups.SemanticActionMonoid
import OAI.GroupTheory.SimpleOvergroups.SemanticActions
import OAI.GroupTheory.SimpleOvergroups.SemanticDouble

namespace OAI


noncomputable section
open scoped Classical

namespace SourceActionMonoid
variable {V Y : Type*} [Group V] [MulAction V Y]
instance monoidWithZero : MonoidWithZero (M V Y) where
  __ := (inferInstance : Monoid (M V Y))
  zero := omega
  zero_mul := omega_mul
  mul_zero := mul_omega
end SourceActionMonoid

namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding EffectiveNames NamedAction StageConstruction
namespace SemanticTests
local instance : Primcodable (ZMod 2) := FiniteAlgebraicEnvelopes.Effect.finitePrimcodable _
local instance : Primcodable (ZMod 3) := FiniteAlgebraicEnvelopes.Effect.finitePrimcodable _

variable {A R : Type} [Primcodable A] [Ring R] [Algebra (ZMod 2) R]
  (π : SemanticMatrix.Raw (ZMod 2) A →ₐ[ZMod 2] R)
  (σ : R → SemanticMatrix.Raw (ZMod 2) A) (hσ : Function.Injective σ)
  {m : ℕ} (C : WordCalculus (FreeMonoid A) m)

abbrev N := MatrixWords.nameOperations (k:=ZMod 2) (n:=7) (MatrixWords.grade C)
abbrev baseC := SemanticMatrix.calculus σ hσ m
abbrev baseI := SemanticMatrix.interpretation π σ hσ (MatrixWords.grade C) m
abbrev doubledC := SemanticDouble.calculus (baseC σ hσ (m:=m))
abbrev I := SemanticDouble.interpretation (N C) (baseC σ hσ (m:=m)) (baseI π σ hσ C)
abbrev N₂ := SemanticDouble.N₂ (N C)
abbrev Symbols := Letter (SemanticDouble.GroupName (G:=MatrixWords.Word (ZMod 2) A 7))
  (SemanticDouble.PointName (G:=MatrixWords.Word (ZMod 2) A 7) (X:=MatrixWords.Point (ZMod 2) A 7))

abbrev evaluation : FreeMonoid (Symbols (A:=A)) →* SourceActionMonoid.M
    (SourceEnlargement.Double.W (Q R)) (SourceEnlargement.Double.Y (Q:=Q R) (X:=X R)) :=
  SemanticActionMonoid.wordMap (I π σ hσ C)

 theorem evaluation_surjective (hπ : Function.Surjective π) :
    Function.Surjective (evaluation π σ hσ C) :=
  SemanticActionMonoid.wordMap_surjective (I π σ hσ C)
    (SemanticDouble.groupValue_surjective (N C) (baseC σ hσ (m:=m)) (baseI π σ hσ C)
      (SemanticMatrix.groupValue_surjective π hπ))
    (SemanticDouble.pointValue_surjective (N C) (baseC σ hσ (m:=m)) (baseI π σ hσ C)
      (SemanticMatrix.groupValue_surjective π hπ) (SemanticMatrix.pointValue_surjective π hπ))

 theorem full (hs : ∀ a, σ (π a) = C.collect (ZMod 2) a)
    (f : List A → Part (List A))
    (hf : ∀ u, (C.normal (FreeMonoid.ofList u)).toList ∈ f u)
    (w : List (Symbols (A:=A))) :
    (N₂ C).totalTest (I π σ hσ C).gkey (I π σ hσ C).xkey w ∈
      EffectiveNames.Double.test (IdempotentNames.name (k:=ZMod 2))
        (IdempotentNames.name (k:=ZMod 3)) (MatrixWords.grade C) C.omega.toList f w := by
  apply Operations.test_full _ _ _ _ _ (d:=(N₂ C).wordCost w) ?_ ?_ w le_rfl
  · intro g hg
    apply SemanticDouble.partialGroupKey_full (N C) (baseC σ hσ (m:=m)) (baseI π σ hσ C) _ g hg
    intro v hv
    exact SemanticMatrix.partialGroupKey_full π σ hσ C hs f v hv (fun u _ => hf u)
  · intro x hx
    apply SemanticDouble.partialPointKey_full (N C) (baseC σ hσ (m:=m)) (baseI π σ hσ C) _ x hx
    intro y hy
    exact SemanticMatrix.partialPointKey_full π σ hσ C hs f y hy (fun u _ => hf u)

 theorem keys_eq_iff (u v : List (Symbols (A:=A))) :
    (N₂ C).totalTest (I π σ hσ C).gkey (I π σ hσ C).xkey u =
      (N₂ C).totalTest (I π σ hσ C).gkey (I π σ hσ C).xkey v ↔
    evaluation π σ hσ C (FreeMonoid.ofList u) = evaluation π σ hσ C (FreeMonoid.ofList v) :=
  SemanticActionMonoid.totalTest_eq_iff (I π σ hσ C)
    (SemanticDouble.groupKey_injective (baseC σ hσ (m:=m))
      (SemanticMatrix.groupKey_injective σ hσ))
    (SemanticDouble.pointKey_injective (baseC σ hσ (m:=m))
      (SemanticMatrix.pointKey_injective σ hσ)) u v

 theorem keys_eq_none (w : List (Symbols (A:=A))) :
    (N₂ C).totalTest (I π σ hσ C).gkey (I π σ hσ C).xkey w = none ↔
      evaluation π σ hσ C (FreeMonoid.ofList w) = 0 := by
  exact keys_eq_iff π σ hσ C w [.inr (.inr none)]

end SemanticTests
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
