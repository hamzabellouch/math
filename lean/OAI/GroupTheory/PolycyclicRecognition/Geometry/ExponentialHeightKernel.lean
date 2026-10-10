import OAI.GroupTheory.PolycyclicRecognition.Geometry.HeightFactorization
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentExponential
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace OAI

/-! # The group height kernel from exponential coordinates

A representation strictly upper triangular on the canonical Lie kernel is
unipotent on the group height kernel. Thus the already proved chain-packing
theorem applies without a separate group-kernel hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open PositiveTriangular
open scoped Matrix.Norms.Operator

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {a : ℕ} (T : TriangularAdjoint L a)
  {G W : Type*} [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
  (q : HeightSpace T.character ≃ₗ[ℝ] W)
  (Exp : L → G) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))

include T q Exp hπExp

theorem integrated_height_surjective : Function.Surjective π := by
  intro w
  obtain ⟨x, hx⟩ := heightProjection_surjective T.character (q.symm w.toAdd)
  refine ⟨Exp x, ?_⟩
  apply Multiplicative.ext
  rw [hπExp, hx, q.apply_symm_apply]

/-- In global exponential coordinates the height map is a quotient map.
This uses only the finite-dimensional open mapping theorem, so no separate
openness hypothesis on the integrated homomorphism is needed. -/
theorem integrated_height_isQuotientMap
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L]
    [T2Space L] [FiniteDimensional ℝ L] [TopologicalSpace G]
    (e : L ≃ₜ G) (he : ∀ x, Exp x = e x) :
    Topology.IsQuotientMap (fun g => (π g).toAdd) := by
  let f : L →ₗ[ℝ] W := q.toLinearMap.comp (heightProjection T.character)
  have hf : Function.Surjective f :=
    q.surjective.comp (heightProjection_surjective T.character)
  let : FiniteDimensional ℝ W := Module.Finite.of_surjective f hf
  have hq : Topology.IsQuotientMap f :=
    (f.isOpenMap_of_finiteDimensional hf).isQuotientMap
      f.continuous_of_finiteDimensional hf
  apply e.isQuotientMap.of_comp_isQuotientMap
  convert hq using 1
  funext x
  change (π (e x)).toAdd = f x
  rw [← he x]
  exact hπExp x

theorem unipotent_height_kernel_of_exponential_representation
    (hExp : Function.Surjective Exp) {m : ℕ}
    (ρ : G →* positiveTriangular m) (j : L →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (hρExp : ∀ x, matrix (ρ (Exp x)) = NormedSpace.exp (j x))
    (hstrict : ∀ x ∈ T.kernelIdeal, StrictUpper (j x)) :
    ∀ g, π g = 1 → StrictUpper (matrix (ρ g) - 1) := by
  intro g hg
  obtain ⟨x, rfl⟩ := hExp g
  have hp : heightProjection T.character x = 0 := by
    apply q.injective
    rw [map_zero, ← hπExp, hg]
    rfl
  have hx : x ∈ T.kernelIdeal := (Submodule.Quotient.mk_eq_zero _).mp hp
  rw [hρExp]
  exact (hstrict x hx).exp_sub_one

/-- Polynomial chain packing for the integrated canonical height follows
from a compatible triangular representation and its Lie-kernel strictness. -/
theorem polynomialBoundedChainPacking_of_exponential_representation
    [MetricSpace G] [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
    (hExp : Function.Surjective Exp) {m : ℕ} [NeZero m]
    (ρ : G →* positiveTriangular m) (j : L →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (hρExp : ∀ x, matrix (ρ (Exp x)) = NormedSpace.exp (j x))
    (hstrict : ∀ x ∈ T.kernelIdeal, StrictUpper (j x))
    (hquot : Topology.IsQuotientMap (fun g => (π g).toAdd))
    (hρ : Topology.IsInducing (fun g => matrix (ρ g))) :
    PolynomialBoundedChainPacking (fun g => (π g).toAdd) := by
  exact polynomialBoundedChainPacking_of_unipotent_kernel π ρ
    (integrated_height_surjective T q Exp π hπExp) hquot hρ
    (unipotent_height_kernel_of_exponential_representation T q Exp π hπExp
      hExp ρ j hρExp hstrict)

/-- The exponential-coordinate version of the packing bridge has no assumed
topological quotient property and no assumed group-kernel unipotence. -/
theorem polynomialBoundedChainPacking_of_exponential_chart
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L]
    [T2Space L] [FiniteDimensional ℝ L]
    [MetricSpace G] [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
    (e : L ≃ₜ G) (he : ∀ x, Exp x = e x) {m : ℕ} [NeZero m]
    (ρ : G →* positiveTriangular m) (j : L →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (hρExp : ∀ x, matrix (ρ (Exp x)) = NormedSpace.exp (j x))
    (hstrict : ∀ x ∈ T.kernelIdeal, StrictUpper (j x))
    (hρ : Topology.IsInducing (fun g => matrix (ρ g))) :
    PolynomialBoundedChainPacking (fun g => (π g).toAdd) := by
  have hExp : Function.Surjective Exp := by
    simpa only [funext he] using e.surjective
  exact polynomialBoundedChainPacking_of_exponential_representation T q Exp π hπExp
    hExp ρ j hρExp hstrict (integrated_height_isQuotientMap T q Exp π hπExp e he) hρ

end PolycyclicRecognition

end

end OAI
