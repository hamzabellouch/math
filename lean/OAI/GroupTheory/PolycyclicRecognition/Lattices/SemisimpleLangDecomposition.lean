import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleLangTransversal
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialDerivationAction

namespace OAI

/-! # Inner perturbations of a semisimple nilpotent automorphism

The fixed part of the Lang transversal is retained. It commutes with the
semisimple automorphism, while the moving part is absorbed by conjugation.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem semisimple_lang_decomposition (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : Module.End.IsSemisimple A.toLinearMap) (u : L) :
    ∃ v w : L, v ∈ (A.toLinearMap - (1 : Module.End ℝ L)).range ∧
      A w = w ∧ u = v⁻¹ * w * A v := by
  let B : Module.End ℝ L := A.toLinearMap - 1
  have hB : B.IsSemisimple := semisimple_sub_one A.toLinearMap hA
  let P := semisimpleKernelProjection B hB
  have hs : Function.Surjective (fun x : L => (x - P x)⁻¹ * P x * A (x - P x)) :=
    (semisimple_lang_transversal_bijective A hA).surjective
  obtain ⟨x, hx⟩ := hs u
  refine ⟨x - P x, P x, ?_, ?_, hx.symm⟩
  · exact Submodule.sub_projection_mem (semisimple_kernel_range_isCompl B hB) x
  · exact sub_eq_zero.mp (semisimpleKernelProjection_mem B hB x)

theorem semisimple_inner_twist (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : Module.End.IsSemisimple A.toLinearMap) (u : L) :
    ∃ v w : L, A w = w ∧
      Commute (PolynomialExponentialCoordinates.groupAutomorphism (P := C) A) (MulAut.conj w) ∧
      MulAut.conj v * (MulAut.conj u * PolynomialExponentialCoordinates.groupAutomorphism (P := C) A) * (MulAut.conj v)⁻¹ =
        MulAut.conj w * PolynomialExponentialCoordinates.groupAutomorphism (P := C) A := by
  obtain ⟨v, w, _, hw, hu⟩ := semisimple_lang_decomposition A hA u
  let S := PolynomialExponentialCoordinates.groupAutomorphism (P := C) A
  have hSv : S v = A v := rfl
  have hSw : S w = w := hw
  refine ⟨v, w, hw, ?_, ?_⟩
  · apply DFunLike.ext
    intro x
    change S (w * x * w⁻¹) = w * S x * w⁻¹
    rw [map_mul, map_mul, map_inv, hSw]
  · apply DFunLike.ext
    intro x
    change v * (u * S (v⁻¹ * x * v) * u⁻¹) * v⁻¹ = w * S x * w⁻¹
    rw [hu, ← hSv]
    simp only [map_mul, map_inv]
    group

end PolycyclicRecognition

end

end OAI
