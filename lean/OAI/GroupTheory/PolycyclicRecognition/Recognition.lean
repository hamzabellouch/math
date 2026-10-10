import OAI.GroupTheory.PolycyclicRecognition.GromovImport
import OAI.GroupTheory.PolycyclicRecognition.RecognitionFromGromov
import OAI.GroupTheory.PolycyclicRecognition.ConditionalBoundedHeight
import OAI.GroupTheory.PolycyclicRecognition.CoarseFiniteGeneration
import OAI.GroupTheory.PolycyclicRecognition.FiniteCovolumeLattice

namespace OAI

/-!
# Unconditional quasi-isometric recognition of virtually polycyclic groups

The geometric height theorem, finiteness and duality endgame, and solvable
lattice realization combine with Gromov's polynomial-growth theorem to yield
virtual polycyclicity and a finite-index uniform-lattice model.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra MeasureTheory
open scoped Manifold NNReal

/-- The main group recognition theorem and its uniform-lattice realization. -/
theorem group_recognition
    {P J : Type} [Group P] [Group J] [Group.FG P] [Group.FG J]
    (e : GroupCoarseEquivalence P J) (hP : IsVirtuallyPolycyclic P) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) :=
  group_recognition_of_gromov (fun _ => gromovPolynomialGrowthInput) e hP

/-- A group quasi-isometric to a uniform solvable Lie lattice is virtually
isomorphic to a uniform lattice in a connected simply connected solvable Lie
group. The new ambient Lie group is allowed to differ from the original one. -/
theorem uniform_lattice_recognition
    (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier)
    (hΛ : IsUniformLattice Λ)
    {J : Type} [Group J] [Group.FG J] (e : GroupCoarseEquivalence Λ J) :
    ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
      ∃ (R : SimplyConnectedSolvableLieModel) (Δ : Subgroup R.carrier),
        IsUniformLattice Δ ∧ Nonempty (Γ ≃* Δ) :=
  uniform_lattice_recognition_of_gromov (fun _ => gromovPolynomialGrowthInput) S Λ hΛ e

/-- The metric formulation, retaining the concrete proper word-metric data. -/
theorem recognition_and_lattice
    {P J : Type} [Group P] [Group J] [MetricSpace P] [MetricSpace J]
    [IsIsometricSMul P P] [IsIsometricSMul J J] [Group.FG P] [Group.FG J]
    [DiscreteTopology J] [ProperSpace J]
    [MeasurableSpace J] [BorelSpace J] [MeasurableMul J]
    (e : MetricQuasiEquivalence P J) (hP : IsVirtuallyPolycyclic P)
    (CP : LinearMetricChains P)
    (hPfinite : ∀ r : ℝ, (Metric.closedBall (1 : P) r).Finite) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) :=
  recognition_and_lattice_of_gromov (fun _ => gromovPolynomialGrowthInput) e hP CP hPfinite

/-- The full finite-covolume lattice corollary. Finite generation of the source
lattice follows from the given coarse equivalence. The existing discrete
subgroup theorem then supplies its polycyclicity, without a uniformity input. -/
theorem lattice_recognition
    (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier)
    (hΛ : IsFiniteCovolumeLattice Λ)
    {J : Type} [Group J] [Group.FG J] (e : GroupCoarseEquivalence Λ J) :
    ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
      ∃ (R : SimplyConnectedSolvableLieModel) (Δ : Subgroup R.carrier),
        IsUniformLattice Δ ∧ Nonempty (Γ ≃* Δ) := by
  obtain ⟨d⟩ := S.nonempty_properChainMetric geodesicMetricExistenceInput
  let := d.compatibleMetric
  let : Group.FG Λ := e.symm.finitelyGenerated
  let : DiscreteTopology Λ := hΛ.1
  have hpoly : IsPolycyclic Λ :=
    isPolycyclic_finitelyGenerated_discrete_solvableLieGroup
      (E := S.modelSpace) Λ
  exact (group_recognition e hpoly.isVirtuallyPolycyclic).2

/-- The standalone geometric main theorem of the paper. -/
theorem main_uniform_bounded_height
    (R : SimplyConnectedSolvableLieModel) (d : ProperChainMetric R.carrier)
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) a)
    (huni : ModelIsUnimodular R)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier → R.carrier)
    (hExp : IsGroupExponential Exp) (π : R.carrier →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) :
    letI := d.compatibleMetric
    ∃ A : Subgroup (W ≃ₗ[ℝ] W), Set.Finite (A : Set (W ≃ₗ[ℝ] W)) ∧
      ∀ K C : ℝ, 1 ≤ K → 0 ≤ C → ∃ B : ℝ, 0 ≤ B ∧
        ∀ F : SelfQuasiIsometry R.carrier K C, ∃ AF : A, ∀ g,
          ‖(π (F.toFun g)).toAdd - ((π (F.toFun 1)).toAdd + AF.val (π g).toAdd)‖ ≤ B :=
  uniform_bounded_height R d T huni q Exp hExp π hπExp

end PolycyclicRecognition

end

end OAI
