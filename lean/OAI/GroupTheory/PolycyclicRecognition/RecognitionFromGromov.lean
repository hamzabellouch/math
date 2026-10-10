import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConditionalGroupRecognition
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RecognitionWithoutKMN

namespace OAI

/-! # Recognition from the polynomial-growth theorem

The geometric height estimate, lattice realization, finiteness, and duality
combine with the exact polynomial-growth statement of Gromov's theorem.
-/
noncomputable section
namespace PolycyclicRecognition
open Module LieAlgebra MeasureTheory
open scoped Manifold NNReal
attribute [local instance] stationaryL2Action zeroMeanL2Action

theorem recognition_and_lattice_of_gromov
    (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
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
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  classical
  obtain ⟨Γ, hΓ, S, Λ, hΛ, ⟨iso⟩⟩ :=
    exists_uniform_solvable_lattice_of_virtuallyPolycyclic dekimpeLatticeRealizationInput P hP
  obtain ⟨R, a, T, dS, dR, hmodel⟩ :=
    exists_intrinsic_height_model_with_controlled_contraction cornulierTesseraModelInput
      geodesicMetricExistenceInput lieRiemannianMetricInput matrixLieDifferentialInput S
  let := dS.compatibleMetric
  let := dR.toProperChainMetric.compatibleMetric
  let := dS.proper_compatibleMetric
  let := dS.isometric_compatibleMetric
  let := dR.toProperChainMetric.proper_compatibleMetric
  let := dR.toProperChainMetric.isometric_compatibleMetric
  let : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  let : IsTopologicalGroup R.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, R.modelSpace)) ⊤
  let : MeasurableSpace R.carrier := borel _
  let : BorelSpace R.carrier := ⟨rfl⟩
  obtain ⟨⟨eSR⟩, ⟨c⟩, q, Exp, π, hExp, hπExp, _, _, K, hK, hπLip⟩ := hmodel
  obtain ⟨ePS⟩ := nonempty_original_lattice_comparison CP hPfinite Γ hΓ S Λ hΛ iso dS
  let u := e.symm.trans (ePS.trans eSR)
  let m : Measure R.carrier := Measure.haar
  let : m.IsMulRightInvariant :=
    SimplyConnectedSolvableLieModel.isMulRightInvariant_of_lattice_comparison
      isPolycyclic_uniformLattice_solvableLieGroup S R Λ hΛ
      dS dR.toProperChainMetric eSR m
  have hπ : LipschitzWith (⟨K, hK⟩ : ℝ≥0) (fun g => (π g).toAdd) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    exact hπLip x y
  have hunimod (x : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) :
      LinearMap.trace ℝ _ (ad ℝ _ x) = 0 :=
    trace_ad_eq_zero_of_intrinsic_kernel_haar T q Exp hExp π hπ.continuous hπExp m x
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel ℝ
    (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier)
  let H := LieSubalgebra.engel ℝ x
  let : H.IsCartanSubalgebra := hx
  obtain ⟨M⟩ := nonempty_cartanWordModel H T
  have hheight := M.exists_uniform_height_intrinsic T hunimod q Exp hExp
    m π hπExp hπ
    dR.minimizing_compatibleMetric remezPolynomialInput geodesicMetricExistenceInput
  exact recognition_and_lattice_of_uniform_normalized_height_proved dekimpeLatticeRealizationInput
    e hP hPfinite T _ q π Exp hExp hπExp u gromov (M.supportIn T hunimod q)
    hπ c dR.minimizing_compatibleMetric hheight


theorem group_recognition_of_gromov
    (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
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
  exact recognition_and_lattice_of_gromov gromov
    (e.metric CP CJ hPfinite hJfinite) hP CP hPfinite

/-- In particular a group quasi-isometric to a uniform solvable Lie lattice
has a finite-index subgroup which is a uniform solvable Lie lattice. -/
theorem uniform_lattice_recognition_of_gromov
    (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
    (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier)
    (hΛ : IsUniformLattice Λ)
    {J : Type} [Group J] [Group.FG J] (e : GroupCoarseEquivalence Λ J) :
    ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
      ∃ (R : SimplyConnectedSolvableLieModel) (Δ : Subgroup R.carrier),
        IsUniformLattice Δ ∧ Nonempty (Γ ≃* Δ) := by
  have hpoly := isPolycyclic_uniformLattice_solvableLieGroup S Λ hΛ
  let := hpoly.finitelyGenerated
  exact (group_recognition_of_gromov gromov e hpoly.isVirtuallyPolycyclic).2


end PolycyclicRecognition

end

end OAI
