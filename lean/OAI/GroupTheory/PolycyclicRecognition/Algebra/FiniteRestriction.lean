import OAI.GroupTheory.PolycyclicRecognition.Algebra.RestrictionEquivalence
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteIntegralRepresentations
import Mathlib.RepresentationTheory.Subrepresentation

namespace OAI

/-! # Restriction through a surjective group homomorphism preserves finite generation -/

noncomputable section
namespace PolycyclicRecognition

open Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G J : Type} [Group G] [Group J]
  (f : J →* G) (A : Rep k G)

def restrictionModuleEquiv :
    A.ρ.asModule ≃ₗ[k] (Rep.res f A).ρ.asModule :=
  A.ρ.asModuleEquiv.trans (Rep.res f A).ρ.asModuleEquiv.symm

theorem restriction_span_of_span (hf : Function.Surjective f) (s : Set A.ρ.asModule)
    (hs : Submodule.span k[G] s = ⊤) :
    Submodule.span k[J] (restrictionModuleEquiv k f A '' s) = ⊤ := by
  let p := Submodule.span k[J] (restrictionModuleEquiv k f A '' s)
  let pR := Subrepresentation.ofSubmodule' p
  let q : Subrepresentation A.ρ :=
    { toSubmodule := pR.toSubmodule
      apply_mem_toSubmodule g a ha := by
        obtain ⟨j, rfl⟩ := hf g
        exact pR.apply_mem_toSubmodule j ha }
  have hsq : s ⊆ q.asSubmodule := by
    intro a ha
    change restrictionModuleEquiv k f A a ∈ p
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  have hq : q.asSubmodule = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Submodule.span_le.mpr hsq
  apply top_unique
  intro a _
  have ha : A.ρ.asModuleEquiv.symm ((Rep.res f A).ρ.asModuleEquiv a) ∈ q.asSubmodule := by
    rw [hq]
    trivial
  exact ha

theorem finite_restriction_of_surjective (hf : Function.Surjective f)
    [Module.Finite k[G] A.ρ.asModule] :
    Module.Finite k[J] (Rep.res f A).ρ.asModule := by
  classical
  obtain ⟨s, hsf, hs⟩ := Submodule.fg_def.mp (Module.Finite.fg_top :
    (⊤ : Submodule k[G] A.ρ.asModule).FG)
  exact Module.Finite.of_fg_top (Submodule.fg_def.mpr
    ⟨restrictionModuleEquiv k f A '' s, hsf.image _, restriction_span_of_span k f A hf s hs⟩)

end PolycyclicRecognition

end

end OAI
