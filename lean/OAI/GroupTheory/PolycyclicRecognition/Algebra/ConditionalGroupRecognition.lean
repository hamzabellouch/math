import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConditionalRecognition
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteWordMetric

namespace OAI

/-! # The metric-free group formulation of conditional recognition

For finitely generated groups, `GroupCoarseEquivalence` expresses the
finite-difference control of quasi-isometry in word metrics. The proof
constructs the finite word metrics and their linear chains explicitly.
-/

noncomputable section
namespace PolycyclicRecognition

/-- Recognition of a finitely generated group coarsely equivalent to a
virtually polycyclic group, with no auxiliary metric assumptions. -/
theorem group_recognition_of_published_inputs
    (inputs : PublishedRecognitionInputs)
    {P J : Type} [Group P] [Group J] [Group.FG P] [Group.FG J]
    (e : GroupCoarseEquivalence P J) (hP : IsVirtuallyPolycyclic P) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨dP, hPd, hPi, hPp, ⟨CP⟩⟩ := exists_finite_word_metric P
  let := dP
  let := hPd
  let := hPi
  let := hPp
  obtain ⟨dJ, hJd, hJi, hJp, ⟨CJ⟩⟩ := exists_finite_word_metric J
  let := dJ
  let := hJd
  let := hJi
  let := hJp
  let : MeasurableSpace J := borel _
  let : BorelSpace J := ⟨rfl⟩
  have hPfinite (r : ℝ) : (Metric.closedBall (1 : P) r).Finite :=
    (isCompact_closedBall (1 : P) r).finite_of_discrete
  have hJfinite (r : ℝ) : (Metric.closedBall (1 : J) r).Finite :=
    (isCompact_closedBall (1 : J) r).finite_of_discrete
  exact recognition_and_lattice_of_published_inputs inputs
    (e.metric CP CJ hPfinite hJfinite) hP CP hPfinite

/-- In particular a group quasi-isometric to a uniform solvable Lie lattice
has a finite-index subgroup which is a uniform solvable Lie lattice. -/
theorem uniform_lattice_recognition_of_published_inputs
    (inputs : PublishedRecognitionInputs)
    (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier)
    (hΛ : IsUniformLattice Λ)
    {J : Type} [Group J] [Group.FG J] (e : GroupCoarseEquivalence Λ J) :
    ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
      ∃ (R : SimplyConnectedSolvableLieModel) (Δ : Subgroup R.carrier),
        IsUniformLattice Δ ∧ Nonempty (Γ ≃* Δ) := by
  have hpoly := inputs.farbWeinberger S Λ hΛ
  let := hpoly.finitelyGenerated
  exact (group_recognition_of_published_inputs inputs e hpoly.isVirtuallyPolycyclic).2

end PolycyclicRecognition

end

end OAI
