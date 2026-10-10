import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponentialNaturality
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularLieDifferential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput

namespace OAI

/-! # Exponential compatibility of triangular realizations

The matrix derivative determines each one-parameter subgroup. An inducing
realization and its matrix differential therefore give exponential-linear
compatibility.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

theorem matrixLieDifferential_exponential
    (differential : MatrixLieDifferentialInput)
    (S : SimplyConnectedSolvableLieModel) (n : ℕ)
    (ρ : S.carrier →* Matrix.GeneralLinearGroup (Fin n) ℝ)
    (hc : Continuous ρ) (hi : Function.Injective ρ) :
    ∃ j : GroupLieAlgebra (𝓘(ℝ, S.modelSpace)) S.carrier →ₗ⁅ℝ⁆
        Matrix (Fin n) (Fin n) ℝ,
      Function.Injective j ∧
      ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, S.modelSpace)) S.carrier → S.carrier),
        IsGroupExponential Exp → ∀ x, ρ (Exp x) = algebraExpUnit (j x) := by
  obtain ⟨j, hd⟩ := differential S n ρ hc hi
  have hj := matrixLieDifferential_injective S n ρ hi j hd
  refine ⟨j, hj, ?_⟩
  intro Exp hExp x
  exact hom_exp_eq_algebraExpUnit hExp ρ j.toLinearMap.toContinuousLinearMap hd x

theorem exponentialLinearRealizationInput_of_triangular
    (differential : MatrixLieDifferentialInput)
    (S : SimplyConnectedSolvableLieModel) (d : ProperChainMetric S.carrier)
    (realize : letI := d.compatibleMetric
      ∀ (a : ℕ) (T : TriangularAdjoint
        (GroupLieAlgebra (𝓘(ℝ, S.modelSpace)) S.carrier) a),
        OnshuusPostRealizationInput T) :
    letI := d.compatibleMetric
    ExponentialLinearRealizationInput (EG := S.modelSpace) (G := S.carrier) := by
  let := d.compatibleMetric
  let : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  rintro ⟨a, ⟨T⟩⟩ Exp hExp
  obtain ⟨m, hm, ρ, hind, _hnil⟩ := realize a T Exp hExp
  let σ : S.carrier →* (Matrix (Fin m) (Fin m) ℝ)ˣ :=
    (positiveTriangular m).subtype.comp ρ
  have hσ : Continuous σ := by
    apply Units.continuous_iff.mpr
    refine ⟨hind.continuous, ?_⟩
    have hv : Continuous (fun g => (σ g : Matrix (Fin m) (Fin m) ℝ)) := hind.continuous
    simpa only [Function.comp_def, map_inv] using hv.comp continuous_inv
  have hi : Function.Injective σ := by
    intro x y h
    exact hind.injective (congrArg Units.val h)
  obtain ⟨j, _hj, hexp⟩ := matrixLieDifferential_exponential differential S m σ hσ hi
  exact ⟨m, hm, σ, j, hind, hexp Exp hExp⟩

end PolycyclicRecognition

end

end OAI
