import OAI.GroupTheory.PolycyclicRecognition.Algebra.ClassTwoCommutatorPairing
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Algebra.Module.Submodule.Lattice

namespace OAI

/-! # The exterior bracket onto the central derived layer -/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement IsMulCommutative
variable {G : Type} [Group G]

def centerCommutatorAlternating (h : commutator G ≤ Subgroup.center G) :
    Additive (Abelianization G) [⋀^Fin 2]→ₗ[ℤ] Additive (Subgroup.center G) where
  toFun v := centerCommutatorPairing h (v 0) (v 1)
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp [Function.update, map_add, LinearMap.add_apply]
  map_update_smul' := by
    intro _ v i r x
    fin_cases i <;> simp [Function.update, map_smul, LinearMap.smul_apply]
  map_eq_zero_of_eq' := by
    intro v i j hij hne
    fin_cases i <;> fin_cases j <;> simp_all [centerCommutatorPairing_self]

def centerExteriorBracket (h : commutator G ≤ Subgroup.center G) :
    (⋀[ℤ]^2 (Additive (Abelianization G))) →ₗ[ℤ] Additive (Subgroup.center G) :=
  exteriorPower.alternatingMapLinearEquiv (centerCommutatorAlternating h)

@[simp] theorem centerExteriorBracket_value
    (h : commutator G ≤ Subgroup.center G) (a b : Additive (Abelianization G)) :
    centerExteriorBracket h (exteriorPower.ιMulti ℤ 2 ![a, b]) =
      centerCommutatorPairing h a b :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem centerCommutatorPairing_mem_derived
    (h : commutator G ≤ Subgroup.center G) (a b : Additive (Abelianization G)) :
    ((centerCommutatorPairing h a b).toMul : G) ∈ commutator G := by
  induction a using QuotientGroup.induction_on with | H a =>
    induction b using QuotientGroup.induction_on with | H b =>
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

def centralDerivedSubmodule : Submodule ℤ (Additive (Subgroup.center G)) :=
  ((commutator G).subgroupOf (Subgroup.center G)).toAddSubgroup.toIntSubmodule

theorem centerExteriorBracket_mem_derived
    (h : commutator G ≤ Subgroup.center G) (x : ⋀[ℤ]^2 (Additive (Abelianization G))) :
    centerExteriorBracket h x ∈ centralDerivedSubmodule (G := G) := by
  have hx : x ∈ Submodule.span ℤ (Set.range (exteriorPower.ιMulti ℤ 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv, centerExteriorBracket_value]
    exact centerCommutatorPairing_mem_derived h _ _
  | zero => simpa only [map_zero] using (centralDerivedSubmodule (G := G)).zero_mem
  | add x y _ _ hx hy =>
    simpa only [map_add] using (centralDerivedSubmodule (G := G)).add_mem hx hy
  | smul r x _ hx =>
    simpa only [map_smul] using (centralDerivedSubmodule (G := G)).smul_mem r hx

def centralDerivedExteriorBracket (h : commutator G ≤ Subgroup.center G) :
    (⋀[ℤ]^2 (Additive (Abelianization G))) →ₗ[ℤ] centralDerivedSubmodule (G := G) :=
  (centerExteriorBracket h).codRestrict _ (centerExteriorBracket_mem_derived h)

theorem centerExteriorBracket_range
    (h : commutator G ≤ Subgroup.center G) :
    LinearMap.range (centerExteriorBracket h) = centralDerivedSubmodule (G := G) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact centerExteriorBracket_mem_derived h x
  · let U := (LinearMap.range (centerExteriorBracket h)).toAddSubgroup.toSubgroup
    let P := U.map (Subgroup.center G).subtype
    have hP : commutator G ≤ P := by
      rw [commutator_eq_closure, Subgroup.closure_le]
      rintro _ ⟨a, b, rfl⟩
      refine ⟨(centerCommutatorPairing h (Additive.ofMul (Abelianization.of a))
        (Additive.ofMul (Abelianization.of b))).toMul, ?_, rfl⟩
      exact ⟨exteriorPower.ιMulti ℤ 2 ![Additive.ofMul (Abelianization.of a),
        Additive.ofMul (Abelianization.of b)], centerExteriorBracket_value h _ _⟩
    intro x hx
    obtain ⟨z, hz, he⟩ := hP hx
    have he' : z = x.toMul := Subtype.ext he
    change Additive.ofMul z ∈ LinearMap.range (centerExteriorBracket h) at hz
    simpa only [he', ofMul_toMul] using hz

theorem centralDerivedExteriorBracket_surjective
    (h : commutator G ≤ Subgroup.center G) :
    Function.Surjective (centralDerivedExteriorBracket h) := by
  intro z
  obtain ⟨x, hx⟩ := (show (z : Additive (Subgroup.center G)) ∈
      LinearMap.range (centerExteriorBracket h) by
    rw [centerExteriorBracket_range h]
    exact z.property)
  exact ⟨x, Subtype.ext hx⟩

end PolycyclicRecognition

end

end OAI
