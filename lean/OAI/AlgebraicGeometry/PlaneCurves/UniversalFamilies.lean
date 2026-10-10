import OAI.AlgebraicGeometry.PlaneCurves.MovingConfigurations
import OAI.AlgebraicGeometry.PlaneCurves.UniversalReduction

namespace OAI

/-!
# Universal polynomial families and moving matrix kernels
-/

section

/-!
# Polynomial-coordinate substitution in the actual jet coefficient matrix
-/
noncomputable section
namespace Nagata.Workers.W14

/-- Substitute genuine polynomial coordinate motions into every matrix entry. -/
def parameterMatrix {K σ ρ κ : Type*} [CommRing K]
    (A : Matrix ρ κ (MvPolynomial σ K)) (p : σ → Polynomial K) :
    Matrix ρ κ (Polynomial K) :=
  fun row col => MvPolynomial.eval₂ Polynomial.C p (A row col)

/-- Evaluating after polynomial-coordinate substitution equals evaluating each
coordinate first; the identity is of actual matrices. -/
theorem specialize_parameterMatrix {K σ ρ κ : Type*} [CommRing K]
    (A : Matrix ρ κ (MvPolynomial σ K)) (p : σ → Polynomial K) (s : K) :
    (parameterMatrix A p).map (Polynomial.evalRingHom s) =
      A.map (MvPolynomial.eval (fun j => (p j).eval s)) := by
  have hc : (Polynomial.evalRingHom s).comp (Polynomial.C : K →+* Polynomial K) =
      RingHom.id K := by
    ext x
    simp
  funext row col
  change (Polynomial.evalRingHom s)
      (MvPolynomial.eval₂Hom Polynomial.C p (A row col)) = _
  rw [MvPolynomial.map_eval₂Hom, hc]
  rfl

theorem parameterMatrix_mulVec {K σ ρ κ : Type*} [CommRing K] [Fintype κ]
    (A : Matrix ρ κ (MvPolynomial σ K)) (p : σ → Polynomial K)
    (s : K) (v : κ → K) :
    ((parameterMatrix A p).map (Polynomial.evalRingHom s)).mulVec v =
      Nagata.W27.coefficientLinearMap A (fun j => (p j).eval s) v := by
  rw [specialize_parameterMatrix]
  rfl

/-- Nonzero solutions of the specialized actual jet equations supply a
normalized polynomial coefficient family in their parameter-substituted matrix. -/
theorem normalized_kernel_of_parameter_equations
    {K σ ρ κ : Type*} [Field K] [Infinite K]
    [Fintype κ] [Fintype ρ] [DecidableEq κ] [DecidableEq ρ]
    (A : Matrix ρ κ (MvPolynomial σ K)) (p : σ → Polynomial K) (E : Finset K)
    (hkernel : ∀ s ∉ E, ∃ v : κ → K, v ≠ 0 ∧
      Nagata.W27.coefficientLinearMap A (fun j => (p j).eval s) v = 0) :
    ∃ q : κ → Polynomial K, (∃ i, (q i).coeff 0 ≠ 0) ∧
      (parameterMatrix A p).mulVec q = 0 := by
  apply Nagata.W18.normalized_kernel_of_general_specialized_kernel (parameterMatrix A p) E
  intro s hs
  obtain ⟨v, hv, heq⟩ := hkernel s hs
  exact ⟨v, hv, by rw [parameterMatrix_mulVec]; exact heq⟩

end Nagata.Workers.W14

end
end

section

/-!
# Genuine universal equations along polynomial affine-chart motions
-/
noncomputable section
namespace Nagata.Workers.W14
open Nagata.ProjectiveGeometry

/-- Actual universal homogeneous equations give actual nonzero specialized
kernels along every good polynomial affine-chart motion. -/
theorem universalSupport_general_chart_kernels {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (c : Fin r → Fin 3) (p : Fin r × Fin 2 → Polynomial ℂ)
    (hbase : Function.Injective
      (configurationChartEmbedding c (fun ij => (p ij).eval 0))) :
    ∃ E : Finset ℂ, 0 ∉ E ∧ ∀ s ∉ E,
      ∃ v : Nagata.W27.HomogeneousMonomial d → ℂ, v ≠ 0 ∧
        Nagata.W27.coefficientLinearMap (Nagata.W27.chartPlaneJetMatrix c d m)
          (fun ij => (p ij).eval s) v = 0 := by
  obtain ⟨E, hE0, hE⟩ := chart_polynomial_motion_cofinite c p hbase
  refine ⟨E, hE0, ?_⟩
  intro s hs
  obtain ⟨F, hF, hhom, hmult⟩ := hU
    ⟨configurationChartEmbedding c (fun ij => (p ij).eval s), hE s hs⟩
  apply (Nagata.W27.exists_nonzero_form_iff_chart_kernel c d m
    (fun ij => (p ij).eval s)).1
  refine ⟨⟨F, hhom⟩, hF, ?_⟩
  intro i
  exact order_directChart_of_multiplicity (c i) (fun j => (p (i, j)).eval s) (m i) (hmult i)

/-- Complete algebraic family bridge along genuine moving projective tuples:
from an actual universal system to a polynomial coefficient family with a
nonzero constant coefficient, in the genuine global homogeneous jet matrix. -/
theorem universalSupport_normalized_parameter_family {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (c : Fin r → Fin 3) (p : Fin r × Fin 2 → Polynomial ℂ)
    (hbase : Function.Injective
      (configurationChartEmbedding c (fun ij => (p ij).eval 0))) :
    ∃ q : Nagata.W27.HomogeneousMonomial d → Polynomial ℂ,
      (∃ i, (q i).coeff 0 ≠ 0) ∧
      (parameterMatrix (Nagata.W27.chartPlaneJetMatrix c d m) p).mulVec q = 0 := by
  classical
  obtain ⟨E, _, hE⟩ := universalSupport_general_chart_kernels hU c p hbase
  exact normalized_kernel_of_parameter_equations
    (Nagata.W27.chartPlaneJetMatrix c d m) p E hE

end Nagata.Workers.W14

end
end

section

/-!
# Affine-linear families based at actual projective configurations

The base tuple consists of genuine projective points. Each chosen affine chart
must contain its base point. Arbitrary prescribed scalar normal displacements
are lifted through explicitly given nonzero local normal differentials.
-/
noncomputable section
namespace Nagata.Workers.W14
open Nagata.ProjectiveGeometry

/-- The manuscript's affine-linear motions in the chosen local charts, expressed
as actual coordinate polynomials in the parameter. -/
def affineChartCoordinateMotion {r : ℕ} (c : ConfigurationChart r)
    (base : Fin r → PlanePoint) (velocity : Fin r × Fin 2 → ℂ) :
    Fin r × Fin 2 → Polynomial ℂ :=
  fun ij => Polynomial.C (configurationChartCoordinates₂ c base ij) +
    Polynomial.X * Polynomial.C (velocity ij)

@[simp] theorem affineChartCoordinateMotion_eval {r : ℕ} (c : ConfigurationChart r)
    (base : Fin r → PlanePoint) (velocity : Fin r × Fin 2 → ℂ)
    (s : ℂ) (ij : Fin r × Fin 2) :
    (affineChartCoordinateMotion c base velocity ij).eval s =
      configurationChartCoordinates₂ c base ij + s * velocity ij := by
  simp only [affineChartCoordinateMotion, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

/-- Every actual universal system yields a normalized polynomial family along
arbitrary affine-linear motions based at a genuine distinct configuration. -/
theorem universalSupport_affine_chart_family {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (base : Fin r → PlanePoint) (hbase : Function.Injective base)
    (c : ConfigurationChart r) (hc : InConfigurationChart c base)
    (velocity : Fin r × Fin 2 → ℂ) :
    ∃ q : Nagata.W27.HomogeneousMonomial d → Polynomial ℂ,
      (∃ i, (q i).coeff 0 ≠ 0) ∧
      (parameterMatrix (Nagata.W27.chartPlaneJetMatrix c d m)
        (affineChartCoordinateMotion c base velocity)).mulVec q = 0 := by
  apply universalSupport_normalized_parameter_family hU c
    (affineChartCoordinateMotion c base velocity)
  simpa only [affineChartCoordinateMotion_eval, zero_mul, add_zero,
    configurationChartEmbedding_coordinates c base hc] using hbase

/-- Choose arbitrary scalar normal displacements and simultaneously obtain the
normalized polynomial family of actual universal equations along those motions.
Smoothness-to-differential identification is the explicit `hnonzero` input. -/
theorem universalSupport_family_with_normal_displacements {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (base : Fin r → PlanePoint) (hbase : Function.Injective base)
    (c : ConfigurationChart r) (hc : InConfigurationChart c base)
    (normalDifferential : Fin r → (Fin 2 → ℂ) →ₗ[ℂ] ℂ)
    (hnonzero : ∀ i, normalDifferential i ≠ 0) (displacement : Fin r → ℂ) :
    ∃ velocity : Fin r × Fin 2 → ℂ,
      (∀ i, normalDifferential i (fun j => velocity (i, j)) = displacement i) ∧
      ∃ q : Nagata.W27.HomogeneousMonomial d → Polynomial ℂ,
        (∃ i, (q i).coeff 0 ≠ 0) ∧
        (parameterMatrix (Nagata.W27.chartPlaneJetMatrix c d m)
          (affineChartCoordinateMotion c base velocity)).mulVec q = 0 := by
  choose v hv using fun i =>
    nonzero_linearFunctional_surjective (normalDifferential i) (hnonzero i) (displacement i)
  refine ⟨fun ij => v ij.1 ij.2, hv, ?_⟩
  exact universalSupport_affine_chart_family hU base hbase c hc (fun ij => v ij.1 ij.2)

end Nagata.Workers.W14

end
end

end OAI
