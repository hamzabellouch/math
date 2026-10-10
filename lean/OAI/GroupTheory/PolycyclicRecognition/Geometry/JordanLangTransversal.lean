import OAI.GroupTheory.PolycyclicRecognition.Geometry.JordanTransversalLinearMap
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialLangTransversal

namespace OAI

/-! # Lang transversals for commuting semisimple and unipotent factors -/

noncomputable section
namespace PolycyclicRecognition
open LieModule
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem jordan_lang_transversal_bijective (A S U : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap) :
    let B : Module.End ℝ L := S.toLinearMap - 1
    let hB := semisimple_sub_one S.toLinearMap hS
    let P := semisimpleKernelProjection B hB
    Function.Bijective (fun x : L => (x - P x)⁻¹ * P x * A (x - P x)) := by
  let B : Module.End ℝ L := S.toLinearMap - 1
  have hB : B.IsSemisimple := semisimple_sub_one S.toLinearMap hS
  let P := semisimpleKernelProjection B hB
  let F : ℕ → Submodule ℝ L := fun k => (lowerCentralSeries ℝ L L k).toSubmodule
  have hSp (k : ℕ) (x : L) (hx : x ∈ F k) : S x ∈ F k :=
    LieIdeal.map_lowerCentralSeries_le k (LieIdeal.mem_map hx)
  have hAp (k : ℕ) (x : L) (hx : x ∈ F k) : A x ∈ F k :=
    LieIdeal.map_lowerCentralSeries_le k (LieIdeal.mem_map hx)
  have hPp (k : ℕ) (x : L) (hx : x ∈ F k) : P x ∈ F k :=
    semisimpleKernelProjection_preserves B hB (F k)
      (fun y hy => (F k).sub_mem (hSp k y hy) hy) hx
  let E : Module.End ℝ L := (S.toLinearMap * U.toLinearMap - 1) * (1 - P) + P
  let e : L ≃ₗ[ℝ] L := LinearEquiv.ofBijective E
    (jordan_transversal_linear_bijective S.toLinearMap U.toLinearMap hS hU hSU)
  have he (z : L) : -(z - P z) + P z + A (z - P z) = e z := by
    change -(z - P z) + P z + A (z - P z) =
      (S (U (z - P z)) - (z - P z)) + P z
    have hz : A (z - P z) = S (U (z - P z)) := LinearMap.congr_fun hA _
    rw [hz]
    abel
  apply polynomial_transversal_bijective A P hPp e he
  intro k x hx
  rw [← he]
  exact (F k).add_mem ((F k).add_mem ((F k).neg_mem ((F k).sub_mem hx (hPp k x hx)))
    (hPp k x hx)) (hAp k _ ((F k).sub_mem hx (hPp k x hx)))

theorem jordan_lang_decomposition (A S U : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap) (u : L) :
    ∃ v w : L, v ∈ (S.toLinearMap - (1 : Module.End ℝ L)).range ∧
      S w = w ∧ u = v⁻¹ * w * A v := by
  let B : Module.End ℝ L := S.toLinearMap - 1
  have hB : B.IsSemisimple := semisimple_sub_one S.toLinearMap hS
  let P := semisimpleKernelProjection B hB
  have hs : Function.Surjective (fun x : L => (x - P x)⁻¹ * P x * A (x - P x)) :=
    (jordan_lang_transversal_bijective A S U hS hU hSU hA).surjective
  obtain ⟨x, hx⟩ := hs u
  refine ⟨x - P x, P x, ?_, ?_, hx.symm⟩
  · exact Submodule.sub_projection_mem (semisimple_kernel_range_isCompl B hB) x
  · exact sub_eq_zero.mp (semisimpleKernelProjection_mem B hB x)

end PolycyclicRecognition

end

end OAI
