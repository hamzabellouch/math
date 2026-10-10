import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Transport.ProjectiveDimension

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]

section RestrictionAlongSurjection
universe v
variable {R S : Type v} [Ring R] [Ring S]

open CategoryTheory.Limits

instance restrictScalars_preservesFiniteLimits (f : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{v} f) where
  preservesFiniteLimits _ _ _ := { preservesLimit := fun {_} => inferInstance }

instance restrictScalars_preservesFiniteColimits (f : R →+* S) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{v} f) where
  preservesFiniteColimits _ _ _ := { preservesColimit := fun {_} => inferInstance }

lemma restrictScalars_full (f : R →+* S) (hf : Function.Surjective f) :
    (ModuleCat.restrictScalars.{v} f).Full where
  map_surjective {M N} g := by
    refine ⟨ModuleCat.ofHom { g.hom with map_smul' := ?_ }, ?_⟩
    · intro s m
      obtain ⟨r, rfl⟩ := hf s
      exact g.hom.map_smul r m
    · rfl

lemma restrictScalars_preservesProjectives (f : R →+* S)
    [Module.Projective R ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))] :
    (ModuleCat.restrictScalars.{v} f).PreservesProjectiveObjects where
  projective_obj {P} hP := by
    classical
    let := hP
    let F := ModuleCat.restrictScalars.{v} f
    let Q := F.obj (ModuleCat.of S S)
    obtain ⟨i, hi⟩ := Module.projective_def'.mp (inferInstance : Module.Projective S P)
    let : Module.Projective R (F.obj (ModuleCat.of S (P →₀ S))) := by
      change Module.Projective R (P →₀ Q)
      exact Module.Projective.of_equiv (finsuppLequivDFinsupp R).symm
    let : Module.Projective R (F.obj P) := Module.Projective.of_split
      (F.map (ModuleCat.ofHom i)).hom
      (F.map (ModuleCat.ofHom (Finsupp.linearCombination S id))).hom (by
        ext x
        exact DFunLike.congr_fun hi x)
    exact inferInstance

lemma finite_restrictScalars (f : R →+* S) (hf : Function.Surjective f)
    (M : ModuleCat.{v} S) [Module.Finite S M] :
    Module.Finite R ((ModuleCat.restrictScalars f).obj M) := by
  let N := (ModuleCat.restrictScalars f).obj M
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := S) (M := M)
  refine ⟨s, ?_⟩
  apply top_unique
  intro x hx
  have hx' : (x : M) ∈ Submodule.span S (s : Set M) := by rw [hs]; trivial
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    obtain ⟨r, rfl⟩ := hf a
    exact Submodule.smul_mem (Submodule.span R (show Set N from (s : Set M))) r ih

lemma littleFinitisticDimension_le_restrictScalars (f : R →+* S)
    (hf : Function.Surjective f)
    [Module.Projective R ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))] :
    littleFinitisticDimension S ≤ littleFinitisticDimension R := by
  let := restrictScalars_full f hf
  let := restrictScalars_preservesProjectives f
  refine iSup_le fun M => iSup_le fun hfg => iSup_le fun hpd => ?_
  let := hfg
  have heq := projectiveDimension_fullyFaithful (ModuleCat.restrictScalars f) M
  rw [← heq]
  exact le_iSup_of_le ((ModuleCat.restrictScalars f).obj M)
    (le_iSup_of_le (finite_restrictScalars f hf M)
      (le_iSup_of_le (by rwa [heq]) le_rfl))

lemma bigFinitisticDimension_le_restrictScalars (f : R →+* S)
    (hf : Function.Surjective f)
    [Module.Projective R ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))] :
    bigFinitisticDimension S ≤ bigFinitisticDimension R := by
  let := restrictScalars_full f hf
  let := restrictScalars_preservesProjectives f
  refine iSup_le fun M => iSup_le fun hpd => ?_
  have heq := projectiveDimension_fullyFaithful (ModuleCat.restrictScalars f) M
  rw [← heq]
  exact le_iSup_of_le ((ModuleCat.restrictScalars f).obj M)
    (le_iSup_of_le (by rwa [heq]) le_rfl)

end RestrictionAlongSurjection

end LittleFinitistic
end
end
end

end OAI
