import OAI.CategoryTheory.Thomason.Simplicial.PosetSieveNaturality

namespace OAI

section

/-! # Full-fibre restriction maps in each actual finite strict category -/

namespace Thomason.Construction.SieveMap

open CategoryTheory StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n)
  {P Q : Type} [PartialOrder P] [PartialOrder Q]
  (A : Set P) (B : Set Q) (f : P →o Q) (hf : ∀ x, f x ∈ B ↔ x ∈ A)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]
  (hA : IsLowerSet A) (hB : IsLowerSet B)

include hf in
/-- Reflected membership labels commute with the original reflected map. -/
theorem finiteMembership :
    Hom.comp (r.reflect.map (h.posetMap f)) (r.membershipLabel h B hB) =
      r.membershipLabel h A hA := by
  apply Hom.ext
  funext x
  have hn := congrArg (fun k : ((r.categorification h).obj (nerve P)).val ⟶
    StrictPoset.category Q => k.toFun x) (r.posetEvaluation_naturality h f)
  change (r.posetEvaluation h Q).toFun ((r.reflect.map (h.posetMap f)).toFun x) =
    (StrictPoset.map f).toFun ((r.posetEvaluation h P).toFun x) at hn
  change (StrictPoset.map (sieveCharacteristic B hB)).toFun
    ((r.posetEvaluation h Q).toFun ((r.reflect.map (h.posetMap f)).toFun x)) = _
  rw [hn]
  exact congrArg (fun k : P →o Fin 2 => (StrictPoset.map k).toFun
    ((r.posetEvaluation h P).toFun x)) (characteristic A B f hf hA hB)

/-- This is the restriction to full zero fibres of the reflected map itself. -/
noncomputable def finiteFiberMap :
    r.reflectedLabelFiber (r.membershipLabel h A hA) ⟶
      r.reflectedLabelFiber (r.membershipLabel h B hB) :=
  labelFiberMap _ _ 0 (r.reflect.map (h.posetMap f))
    (finiteMembership r A B f hf h hA hB)

/-- Naturality holds in the finite category, not only after lifting it to omega. -/
theorem finiteNaturality :
    r.posetFiberMap h A hA ≫ finiteFiberMap r A B f hf h hA hB =
      r.reflect.map (h.posetMap (restriction A B f hf)) ≫ r.posetFiberMap h B hB := by
  have he : h.posetMap (subposetInclusion A) ≫ h.posetMap f =
      h.posetMap (restriction A B f hf) ≫ h.posetMap (subposetInclusion B) := by
    rw [← h.posetMap_comp, ← h.posetMap_comp, restriction_inclusion]
  have hr := congrArg r.reflect.map he
  rw [r.reflect.map_comp, r.reflect.map_comp] at hr
  apply Hom.ext
  funext x
  apply Subtype.ext
  exact congrArg (fun k : (r.categorification h).obj (nerve A) ⟶
    (r.categorification h).obj (nerve Q) => k.toFun x) hr

/-- The canonical finite sieve identification is an isomorphism. -/
theorem finiteSieve_isIso :
    IsIso (C := Truncated (n+1)) (r.posetFiberMap h A hA) := by
  have : IsIso (h.posetFiberMap A hA) := (h.posetSieveIso A hA).isIso_hom
  exact r.posetFiberMap_isIso_of_omega h A hA

end Thomason.Construction.SieveMap

end

end OAI
