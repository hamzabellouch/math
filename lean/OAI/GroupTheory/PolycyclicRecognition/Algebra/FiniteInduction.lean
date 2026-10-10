import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalInductionExact
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteIntegralRepresentations
import Mathlib.RepresentationTheory.Subrepresentation

namespace OAI

/-! # Finite generation is preserved by subgroup induction -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) (A : Rep k N)

def inductionAtOne (a : A.ρ.asModule) : (Rep.ind N.subtype A).ρ.asModule :=
  (Rep.ind N.subtype A).ρ.asModuleEquiv.symm
    (IndV.mk N.subtype A.ρ 1 (A.ρ.asModuleEquiv a))

theorem induction_span_of_span (s : Set A.ρ.asModule)
    (hs : Submodule.span k[N] s = ⊤) :
    Submodule.span k[G] (inductionAtOne k N A '' s) = ⊤ := by
  let p := Submodule.span k[G] (inductionAtOne k N A '' s)
  let pR := Subrepresentation.ofSubmodule' p
  let u : A ⟶ Rep.res N.subtype (Rep.ind N.subtype A) :=
    Rep.indResHomEquiv N.subtype A (Rep.ind N.subtype A) (𝟙 _)
  have hu (a : A) : u.hom a = IndV.mk N.subtype A.ρ 1 a := rfl
  let q : Subrepresentation A.ρ :=
    { toSubmodule := pR.toSubmodule.comap u.hom.toLinearMap
      apply_mem_toSubmodule n a ha := by
        change u.hom (A.ρ n a) ∈ pR.toSubmodule
        rw [Rep.hom_comm_apply]
        exact pR.apply_mem_toSubmodule (n : G) ha }
  have hsq : s ⊆ q.asSubmodule := by
    intro a ha
    change u.hom (A.ρ.asModuleEquiv a) ∈ pR.toSubmodule
    rw [hu]
    change inductionAtOne k N A a ∈ p
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  have hq : q.asSubmodule = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Submodule.span_le.mpr hsq
  have hone (a : A) : IndV.mk N.subtype A.ρ 1 a ∈ pR.toSubmodule := by
    have ha : A.ρ.asModuleEquiv.symm a ∈ q.asSubmodule := by rw [hq]; trivial
    change u.hom a ∈ pR.toSubmodule at ha
    rwa [hu] at ha
  have hmk (g : G) (a : A) : IndV.mk N.subtype A.ρ g a ∈ pR.toSubmodule := by
    simpa only [Rep.ind, Representation.ind_mk, inv_inv, one_mul] using
      pR.apply_mem_toSubmodule g⁻¹ (hone a)
  have hzero : pR.toSubmodule.mkQ = 0 := by
    apply IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro a
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hmk g a)
  apply top_unique
  intro a _
  have ha := LinearMap.congr_fun hzero ((Rep.ind N.subtype A).ρ.asModuleEquiv a)
  exact (Submodule.Quotient.mk_eq_zero _).mp ha

theorem finite_induction [Module.Finite k[N] A.ρ.asModule] :
    Module.Finite k[G] (Rep.ind N.subtype A).ρ.asModule := by
  classical
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp (Module.Finite.fg_top :
    (⊤ : Submodule k[N] A.ρ.asModule).FG)
  exact Module.Finite.of_fg_top (Submodule.fg_def.mpr
    ⟨inductionAtOne k N A '' s, hsfin.image _, induction_span_of_span k N A s hs⟩)

theorem integralRepresentationFinite_induction
    (A : Rep ℤ N) (hA : IntegralRepresentationFinite N A) :
    IntegralRepresentationFinite G (Rep.ind N.subtype A) := by
  let : Module.Finite ℤ[N] A.ρ.asModule := hA
  exact finite_induction ℤ N A

end PolycyclicRecognition

end

end OAI
