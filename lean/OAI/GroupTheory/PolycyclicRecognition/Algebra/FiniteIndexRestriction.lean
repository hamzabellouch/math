import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SubgroupResolution
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteRestriction
import Mathlib.GroupTheory.Index

namespace OAI

/-! # Finite integral resolutions restrict to finite-index subgroups

A finite set of coset representatives enlarges a generating set over the
ambient group ring to one over the subgroup ring.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex]

theorem integralRepresentationFinite_restrict (A : Rep.{0} ℤ G)
    (hA : IntegralRepresentationFinite G A) :
    IntegralRepresentationFinite H (Rep.res H.subtype A) := by
  classical
  let : Module ℤ A := A.hV2
  let : Module.Finite ℤ[G] A.ρ.asModule := hA
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp (Module.Finite.fg_top :
    (⊤ : Submodule ℤ[G] A.ρ.asModule).FG)
  let C := Quotient (QuotientGroup.rightRel H)
  let : Finite C := Finite.of_equiv (G ⧸ H)
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  let : Finite s := hs.to_subtype
  let gen : C × s → (Rep.res H.subtype A).ρ.asModule := fun j =>
    (Rep.res H.subtype A).ρ.asModuleEquiv.symm
      (A.ρ (Quotient.out j.1) (A.ρ.asModuleEquiv j.2.val))
  let p : Submodule ℤ[H] (Rep.res H.subtype A).ρ.asModule :=
    Submodule.span ℤ[H] (Set.range gen)
  let pR := Subrepresentation.ofSubmodule' p
  have horbit (a : A.ρ.asModule) (ha : a ∈ s) (g : G) :
      A.ρ g (A.ρ.asModuleEquiv a) ∈ pR := by
    let c : C := Quotient.mk (QuotientGroup.rightRel H) g
    let r : G := Quotient.out c
    have hn : g * r⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp
      (Quotient.exact' (Quotient.out_eq' c))
    let n : H := ⟨g * r⁻¹, hn⟩
    have hg : (n : G) * r = g := by simp [n]
    have hr : A.ρ r (A.ρ.asModuleEquiv a) ∈ pR := by
      change (Rep.res H.subtype A).ρ.asModuleEquiv.symm
        (A.ρ r (A.ρ.asModuleEquiv a)) ∈ p
      exact Submodule.subset_span ⟨(c, ⟨a, ha⟩), rfl⟩
    have hm := pR.apply_mem_toSubmodule n hr
    change A.ρ (n : G) (A.ρ r (A.ρ.asModuleEquiv a)) ∈ pR at hm
    simpa only [← Module.End.mul_apply, ← map_mul, hg] using hm
  let q : Subrepresentation A.ρ :=
    { toSubmodule := ⨅ g : G, pR.toSubmodule.comap (A.ρ g)
      apply_mem_toSubmodule g a ha := by
        simp only [Submodule.mem_iInf, Submodule.mem_comap] at ha ⊢
        intro k
        simpa only [← Module.End.mul_apply, ← map_mul] using ha (k * g) }
  have hsq : s ⊆ q.asSubmodule := by
    intro a ha
    change A.ρ.asModuleEquiv a ∈ q.toSubmodule
    simp only [q, Submodule.mem_iInf, Submodule.mem_comap]
    exact horbit a ha
  have hq : q.asSubmodule = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact Submodule.span_le.mpr hsq
  have hp : p = ⊤ := by
    apply top_unique
    intro a _
    have ha : A.ρ.asModuleEquiv.symm ((Rep.res H.subtype A).ρ.asModuleEquiv a) ∈
        q.asSubmodule := by rw [hq]; trivial
    change A.ρ.asModuleEquiv.symm ((Rep.res H.subtype A).ρ.asModuleEquiv a) ∈
      q.toSubmodule at ha
    change (Rep.res H.subtype A).ρ.asModuleEquiv a ∈
      (⨅ g : G, pR.toSubmodule.comap (A.ρ g)) at ha
    have h := ((Submodule.mem_iInf _).mp ha) (1 : G)
    change A.ρ 1 ((Rep.res H.subtype A).ρ.asModuleEquiv a) ∈ pR at h
    rw [map_one] at h
    exact h
  change Module.Finite ℤ[H] (Rep.res H.subtype A).ρ.asModule
  apply Module.Finite.of_fg_top
  rw [← hp]
  exact Submodule.fg_def.mpr ⟨Set.range gen, Set.finite_range gen, rfl⟩

theorem TypeFP.finiteIndex_subgroup {n : ℕ} (hG : TypeFP G n) : TypeFP H n := by
  obtain ⟨P, hP⟩ := hG
  exact ⟨subgroupResolution H P, fun i hi =>
    integralRepresentationFinite_restrict H (P.complex.X i) (hP i hi)⟩

theorem TypeFPInfinity.finiteIndex_subgroup (hG : TypeFPInfinity G) :
    TypeFPInfinity H := fun n => (hG n).finiteIndex_subgroup H

theorem HasFiniteProjectiveResolution.finiteIndex_subgroup
    (hG : HasFiniteProjectiveResolution G) : HasFiniteProjectiveResolution H := by
  obtain ⟨P, d, hP, hd⟩ := hG
  refine ⟨subgroupResolution H P, d,
    fun i => integralRepresentationFinite_restrict H (P.complex.X i) (hP i), ?_⟩
  intro i hi
  exact (Rep.resFunctor H.subtype).map_isZero (hd i hi)

end PolycyclicRecognition

end

end OAI
