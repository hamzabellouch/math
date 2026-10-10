import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleKernelProjection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialLangTransversal

namespace OAI

/-! # A global Lang transversal in the presence of fixed directions

The fixed-space projection and its complementary range preserve the lower
central series. The map u,v ↦ u⁻¹ v A(u), written in these linear coordinates,
is therefore a polynomial bijection even when A has fixed vectors.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

/-- The global coordinate map for twisted conjugacy by a semisimple
nilpotent-group automorphism. Its fixed component is retained explicitly. -/
theorem semisimple_lang_transversal_bijective (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : Module.End.IsSemisimple A.toLinearMap) :
    let B : Module.End ℝ L := A.toLinearMap - 1
    let hB : B.IsSemisimple := semisimple_sub_one A.toLinearMap hA
    let P := semisimpleKernelProjection B hB
    Function.Bijective (fun x : L => (x - P x)⁻¹ * P x * A (x - P x)) := by
  let B : Module.End ℝ L := A.toLinearMap - 1
  have hB : B.IsSemisimple := semisimple_sub_one A.toLinearMap hA
  let P := semisimpleKernelProjection B hB
  change Function.Bijective (fun x : L => (x - P x)⁻¹ * P x * A (x - P x))
  let U : ℕ → Submodule ℝ L := fun k => (lowerCentralSeries ℝ L L k).toSubmodule
  have hApres (k : ℕ) (x : L) (hx : x ∈ U k) : A x ∈ U k :=
    LieIdeal.map_lowerCentralSeries_le k (LieIdeal.mem_map hx)
  have hBpres (k : ℕ) (x : L) (hx : x ∈ U k) : B x ∈ U k :=
    (U k).sub_mem (hApres k x hx) hx
  have hPpres (k : ℕ) (x : L) (hx : x ∈ U k) : P x ∈ U k :=
    semisimpleKernelProjection_preserves B hB (U k) (hBpres k) hx
  let e : L ≃ₗ[ℝ] L := LinearEquiv.ofBijective (B + P)
    (semisimple_add_kernelProjection_bijective B hB)
  apply polynomial_transversal_bijective A P hPpres e
  · intro z
    have hfix : A (P z) = P z :=
      sub_eq_zero.mp (semisimpleKernelProjection_mem B hB z)
    simp only [map_sub, hfix]
    change -(z - P z) + P z + (A z - P z) = A z - z + P z
    abel
  · intro k x hx
    exact (U k).add_mem (hBpres k x hx) (hPpres k x hx)

end PolycyclicRecognition

end

end OAI
