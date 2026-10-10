import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteNormalGeneration
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CharacteristicQuotientAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.MonoidRingOrbitSpan
import Mathlib.RepresentationTheory.Basic

namespace OAI

/-! # The finite module on a normally generated subgroup's abelianization -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def normalAbelianizationAut : G →* MulAut (Abelianization N) :=
  (characteristicQuotientAut (commutator N)).comp (MulAut.conjNormal (H := N))

def normalAbelianizationRepresentation : Representation ℤ G (Additive (Abelianization N)) where
  toFun g := (normalAbelianizationAut N g).toAdditive.toIntLinearEquiv.toLinearMap
  map_one' := by
    ext x
    change Additive.ofMul (normalAbelianizationAut N 1 x.toMul) = x
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x
    change Additive.ofMul (normalAbelianizationAut N (g * h) x.toMul) =
      Additive.ofMul (normalAbelianizationAut N g (normalAbelianizationAut N h x.toMul))
    rw [map_mul]
    rfl

theorem normalAbelianizationRepresentation_apply (g : G) (n : N) :
    normalAbelianizationRepresentation N g (Additive.ofMul (Abelianization.of n)) =
      Additive.ofMul (Abelianization.of (MulAut.conjNormal (H := N) g n)) := rfl

theorem finite_normalAbelianizationModule_of_normalGeneration
    (hN : N.IsFinitelyNormallyGenerated) :
    Module.Finite ℤ[G] (normalAbelianizationRepresentation N).asModule := by
  classical
  obtain ⟨S, hS, hSN⟩ := hN
  have hmem : S ⊆ N := hSN ▸ Subgroup.subset_normalClosure
  let := hS.fintype
  let ρ := normalAbelianizationRepresentation N
  let v : S → ρ.asModule := fun s =>
    ρ.asModuleEquiv.symm (Additive.ofMul (Abelianization.of ⟨s, hmem s.property⟩))
  let T : Finset ρ.asModule := Finset.univ.image v
  let U := Submodule.span ℤ (monoidOrbitSet (Q := G) (T : Set ρ.asModule))
  let β : N →* Multiplicative ρ.asModule :=
    { toFun n := Multiplicative.ofAdd
        (ρ.asModuleEquiv.symm (Additive.ofMul (Abelianization.of n)))
      map_one' := by
        change ρ.asModuleEquiv.symm (Additive.ofMul (Abelianization.of 1)) = 0
        simp
      map_mul' n m := by
        change ρ.asModuleEquiv.symm (Additive.ofMul (Abelianization.of (n * m))) =
          ρ.asModuleEquiv.symm (Additive.ofMul (Abelianization.of n)) +
            ρ.asModuleEquiv.symm (Additive.ofMul (Abelianization.of m))
        rw [map_mul]
        exact ρ.asModuleEquiv.symm.map_add _ _ }
  let B := U.toAddSubgroup.toSubgroup.comap β
  let P := B.map N.subtype
  have hconj : Group.conjugatesOfSet S ⊆ P := by
    intro x hx
    obtain ⟨s, hs, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hc
    let n : N := ⟨s, hmem hs⟩
    refine ⟨MulAut.conjNormal (H := N) g n, ?_, rfl⟩
    change ρ.asModuleEquiv.symm
      (Additive.ofMul (Abelianization.of (MulAut.conjNormal (H := N) g n))) ∈ U
    rw [← normalAbelianizationRepresentation_apply]
    change ρ.asModuleEquiv.symm (ρ g (Additive.ofMul (Abelianization.of n))) ∈ U
    rw [Representation.asModuleEquiv_symm_map_rho]
    exact Submodule.subset_span ⟨g, v ⟨s, hs⟩,
      Finset.mem_image_of_mem v (Finset.mem_univ _), rfl⟩
  have hNP : N ≤ P := by
    rw [← hSN]
    exact (Subgroup.closure_le _).mpr hconj
  have hB : B = ⊤ := by
    apply top_unique
    intro n _
    obtain ⟨m, hm, he⟩ := hNP n.property
    have hmn : m = n := Subtype.ext he
    exact hmn ▸ hm
  apply finite_of_monoidOrbitSpan T
  apply top_unique
  intro x _
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (commutator N)
    (ρ.asModuleEquiv x).toMul
  have hnB : n ∈ B := hB ▸ Subgroup.mem_top n
  change ρ.asModuleEquiv.symm (Additive.ofMul (Abelianization.of n)) ∈ U at hnB
  change Abelianization.of n = (ρ.asModuleEquiv x).toMul at hn
  rw [hn] at hnB
  change ρ.asModuleEquiv.symm (ρ.asModuleEquiv x) ∈ U at hnB
  simpa only [LinearEquiv.symm_apply_apply] using hnB

theorem finite_normalAbelianizationModule_of_abelian_quotient
    [Group.FG G] [IsMulCommutative (G ⧸ N)] :
    Module.Finite ℤ[G] (normalAbelianizationRepresentation N).asModule :=
  finite_normalAbelianizationModule_of_normalGeneration N
    (finitelyNormallyGenerated_of_abelian_quotient N)

end PolycyclicRecognition

end

end OAI
