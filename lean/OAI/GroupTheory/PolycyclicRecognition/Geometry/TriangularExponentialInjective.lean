import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularLocalLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularAdjointEmbedding
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RepresentedExponentialDifferential

namespace OAI

/-! # Global injectivity of the real upper triangular matrix exponential

Its differential is nonsingular at every point, by the real triangular
adjoint calculation. Local injectivity at a logarithm, together with the
already proved trivial exponential kernel, excludes every other logarithm.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Matrix.Norms.Operator ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

theorem realTriangularAlgebra_exp_injective (n : ℕ) :
    Function.Injective (NormedSpace.exp : RealTriangularAlgebra n → RealTriangularAlgebra n) := by
  let A := RealTriangularAlgebra n
  let ρ : A →ₗ⁅ℝ⁆ Matrix (Fin n) (Fin n) ℝ :=
    (Matrix.blockTriangularSubalgebra ℝ ℝ (id : Fin n → Fin n)).val.toLieHom
  obtain ⟨m, ⟨T⟩⟩ := nonempty_triangularAdjoint_of_triangular_representation
    ρ Subtype.val_injective (fun x => x.property)
  intro a b hab
  let D : A →L[ℝ] A := fderiv ℝ NormedSpace.exp b
  have hD : Function.Injective D := by
    intro x y hxy
    apply represented_exponential_differential_injective T (LieHom.id : A →ₗ⁅ℝ⁆ A)
      Function.injective_id b
    exact hxy
  have hsurj : Function.Surjective D :=
    (LinearMap.injective_iff_surjective).mp hD
  let e : A ≃L[ℝ] A :=
    (LinearEquiv.ofBijective D.toLinearMap ⟨hD, hsurj⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt (NormedSpace.exp : A → A) e.toContinuousLinearMap b :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) b).differentiableAt.hasFDerivAt
  have hreg : ContDiffAt ℝ ∞ (NormedSpace.exp : A → A) b :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) b).contDiffAt
  have hs := hreg.hasStrictFDerivAt' hd (by simp)
  let p := hs.toOpenPartialHomeomorph NormedSpace.exp
  exact exp_eq_of_local_injectivity realTriangularAlgebra_exp_kernel
    p.source p.open_source p.injOn hs.mem_toOpenPartialHomeomorph_source hab

end PolycyclicRecognition

end

end OAI
