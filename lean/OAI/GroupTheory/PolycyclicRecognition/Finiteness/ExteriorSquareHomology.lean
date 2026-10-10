import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExteriorSquarePairing

namespace OAI

/-! # Second homology covers twice the exterior square

This holds for arbitrary abelian groups, including torsion. Inverting two turns
the explicit map into a surjection; no finite-rank assumption is imposed here.
-/

noncomputable section
namespace PolycyclicRecognition
variable (A : Type) [CommGroup A]

abbrev exteriorSquareHomology :
    groupHomology.H2 (integralTrivialCoefficient A) →ₗ[ℤ] ⋀[ℤ]^2 (Additive A) :=
  bilinearPairingHomology (exteriorSquarePairing (M := Additive A))

theorem exteriorSquareHomology_antisymmetric (a c : A) :
    exteriorSquareHomology A
      (groupHomology.H2π (integralTrivialCoefficient A) (antisymmetricBarCycle a c)) =
      (2 : ℤ) • exteriorSquareValue (Additive.ofMul a) (Additive.ofMul c) :=
  bilinearPairingHomology_antisymmetric _ (fun x y => exteriorSquareValue_swap y x) a c

theorem exteriorSquareHomology_covers_twice (x : ⋀[ℤ]^2 (Additive A)) :
    ∃ z, exteriorSquareHomology A z = (2 : ℤ) • x := by
  have hx : x ∈ Submodule.span ℤ (Set.range (exteriorPower.ιMulti ℤ 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    refine ⟨groupHomology.H2π (integralTrivialCoefficient A)
      (antisymmetricBarCycle (v 0).toMul (v 1).toMul), ?_⟩
    rw [exteriorSquareHomology_antisymmetric]
    exact congrArg (fun w => (2 : ℤ) • exteriorPower.ιMulti ℤ 2 w) hv.symm
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz⟩ := hx
    obtain ⟨w, hw⟩ := hy
    exact ⟨z + w, by rw [map_add, hz, hw, smul_add]⟩
  | smul r x _ hx =>
    obtain ⟨z, hz⟩ := hx
    refine ⟨r • z, ?_⟩
    rw [map_zsmul, hz, smul_smul, smul_smul, mul_comm]

end PolycyclicRecognition

end

end OAI
