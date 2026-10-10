import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularAdjointEmbedding
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangulableLieModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FaithfulDifferential
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed

namespace OAI

/-!
# The differential of a triangular Lie-group realization

The differential of a continuous injective matrix-group homomorphism
is a Lie algebra homomorphism. Precisely, John M. Lee, *Introduction
to Smooth Manifolds*, second edition, GTM 218 (2013), Problem 20-11(b),
pp.537–538, gives automatic smoothness; Theorem 8.44, p.195, gives the
induced Lie algebra homomorphism; Proposition 8.41, pp.193–195, identifies
the matrix-group Lie algebra with the matrix commutator algebra. Its
injectivity follows from Proposition 7.17, pp.157–158 (see its proof using
Theorem 7.5 and the Global Rank Theorem 4.14(b)).

The input retains only the Lie homomorphism and its equality to the
matrix-valued derivative. Its injectivity is proved using faithful
one-parameter subgroups. The derivative is upper triangular and solvable, and admits a
simultaneous adjoint basis.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

-- The norm-induced and entrywise matrix topologies are definitionally equal,
-- but their different heads prevent inference of the self chart.
local instance matrixModelChartedSpace (n : ℕ) :
    @ChartedSpace (Matrix (Fin n) (Fin n) ℝ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
        (@SeminormedAddCommGroup.toPseudoMetricSpace _
          (@NormedAddCommGroup.toSeminormedAddCommGroup _
            (Matrix.normedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ))))))
      (Matrix (Fin n) (Fin n) ℝ) inferInstance := by
  convert chartedSpaceSelf (Matrix (Fin n) (Fin n) ℝ) using 1
  rfl

/-- The matrix derivative supplied by the precisely cited Lee results.
No injectivity, triangularity or spectral consequence is assumed. -/
def MatrixLieDifferentialInput : Prop :=
  ∀ (S : SimplyConnectedSolvableLieModel) (n : ℕ)
    (ρ : S.carrier →* Matrix.GeneralLinearGroup (Fin n) ℝ),
    Continuous ρ → Function.Injective ρ →
      ∃ d : GroupLieAlgebra (𝓘(ℝ, S.modelSpace)) S.carrier →ₗ⁅ℝ⁆
          Matrix (Fin n) (Fin n) ℝ,
        HasMFDerivAt (𝓘(ℝ, S.modelSpace))
            (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
            (fun g => (ρ g : Matrix (Fin n) (Fin n) ℝ)) 1
            d.toLinearMap.toContinuousLinearMap

open scoped Matrix.Norms.Operator in
/-- Faithfulness of the actual derivative follows from faithfulness of
the group map, without an immersion theorem. -/
theorem matrixLieDifferential_injective
    (S : SimplyConnectedSolvableLieModel) (n : ℕ)
    (ρ : S.carrier →* Matrix.GeneralLinearGroup (Fin n) ℝ)
    (hi : Function.Injective ρ)
    (d : GroupLieAlgebra (𝓘(ℝ, S.modelSpace)) S.carrier →ₗ⁅ℝ⁆
      Matrix (Fin n) (Fin n) ℝ)
    (hd : HasMFDerivAt (𝓘(ℝ, S.modelSpace))
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (fun g => (ρ g : Matrix (Fin n) (Fin n) ℝ)) 1
      d.toLinearMap.toContinuousLinearMap) : Function.Injective d :=
  injective_algebra_differential groupExponential_isGroupExponential ρ hi
    d.toLinearMap.toContinuousLinearMap hd

/-- Differentiating the identically zero entries below the diagonal
preserves upper triangularity. -/
theorem hasMFDerivAt_upperTriangular
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace G] [ChartedSpace E G] {n : ℕ}
    {f : G → Matrix (Fin n) (Fin n) ℝ} {a : G}
    {d : TangentSpace (𝓘(ℝ, E)) a →L[ℝ] Matrix (Fin n) (Fin n) ℝ}
    (hd : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) f a d)
    (hf : ∀ g, (f g).IsUpperTriangular) (v : TangentSpace (𝓘(ℝ, E)) a) :
    (d v).IsUpperTriangular := by
  intro i j hij
  let q₀ : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let q : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
    q₀.toContinuousLinearMap
  have hq : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, ℝ))
      (q ∘ f) a (q.comp d) := q.hasFDerivAt.hasMFDerivAt.comp a hd
  have heq : q ∘ f = fun _ => (0 : ℝ) := by
    funext g
    exact hf g hij
  rw [heq] at hq
  have hz : q.comp d = 0 := by
    rw [← hq.mfderiv, mfderiv_const]
    rfl
  exact congrArg (fun l : TangentSpace (𝓘(ℝ, E)) a →L[ℝ] ℝ => l v) hz

/-- CT's actual closed triangular matrix realization supplies a
simultaneous adjoint basis once the narrow matrix-differential input is
given. The algebraic conclusions come from the proved matrix lemmas. -/
theorem IsRealTriangulable.exists_triangularAdjoint
    (differential : MatrixLieDifferentialInput)
    (S : SimplyConnectedSolvableLieModel) (hS : IsRealTriangulable S) :
    ∃ m : ℕ, Nonempty (TriangularAdjoint
      (GroupLieAlgebra (𝓘(ℝ, S.modelSpace)) S.carrier) m) := by
  obtain ⟨n, ρ, hρ, htri⟩ := hS
  obtain ⟨d, hderiv⟩ := differential S n ρ hρ.continuous hρ.injective
  have hd := matrixLieDifferential_injective S n ρ hρ.injective d hderiv
  apply nonempty_triangularAdjoint_of_triangular_representation d hd
  intro v
  exact hasMFDerivAt_upperTriangular (E := S.modelSpace) hderiv htri v

theorem IsRealTriangulable.lieAlgebra_isSolvable
    (differential : MatrixLieDifferentialInput)
    (S : SimplyConnectedSolvableLieModel) (hS : IsRealTriangulable S) :
    LieAlgebra.IsSolvable (GroupLieAlgebra (𝓘(ℝ, S.modelSpace)) S.carrier) := by
  obtain ⟨n, ρ, hρ, htri⟩ := hS
  obtain ⟨d, hderiv⟩ := differential S n ρ hρ.continuous hρ.injective
  have hd := matrixLieDifferential_injective S n ρ hρ.injective d hderiv
  apply lieAlgebra_isSolvable_of_triangular_representation d hd
  intro v
  exact hasMFDerivAt_upperTriangular (E := S.modelSpace) hderiv htri v

/-- The published CT reduction and faithful differential give the actual
adjoint-basis model, with the metric comparison proved from the three
proper cocompact arrows. -/
theorem exists_triangularAdjoint_metric_model
    (ct : CornulierTesseraModelInput) (metricInput : GeodesicMetricExistenceInput)
    (differential : MatrixLieDifferentialInput) (S : SimplyConnectedSolvableLieModel) :
    ∃ T : SimplyConnectedSolvableLieModel, ∃ m : ℕ,
      Nonempty (TriangularAdjoint
        (GroupLieAlgebra (𝓘(ℝ, T.modelSpace)) T.carrier) m) ∧
      ∃ (dS : ProperChainMetric S.carrier) (dT : ProperChainMetric T.carrier),
        letI := dS.compatibleMetric
        letI := dT.compatibleMetric
        Nonempty (MetricQuasiEquivalence S.carrier T.carrier) := by
  obtain ⟨T, hT, dS, dT, hmetric⟩ := exists_realTriangulable_metric_model ct metricInput S
  obtain ⟨m, hm⟩ := IsRealTriangulable.exists_triangularAdjoint differential T hT
  exact ⟨T, m, hm, dS, dT, hmetric⟩

end PolycyclicRecognition

end

end OAI
