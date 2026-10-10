import OAI.GroupTheory.PolycyclicRecognition.Algebra.RecognitionFromPairRepresentatives
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TransferredPairRepresentatives

namespace OAI

/-! # Recognition from uniform normalized height control

Transferred pairs and a uniform normalized height bound yield virtual
polycyclicity and a finite-index uniform-lattice realization.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Manifold NNReal

theorem recognition_and_lattice_of_uniform_normalized_height
    (dekimpe : DekimpeLatticeRealizationInput)
    (liFP : LiFinitenessInput) (eaFP : ElementaryAmenableFinitenessInput)
    (liPD : LiDualityInput) (bieri : BieriDualityInput)
    {P J : Type} [Group P] [Group J] [MetricSpace P] [MetricSpace J]
    [IsIsometricSMul P P] [IsIsometricSMul J J] [Group.FG P] [Group.FG J]
    [DiscreteTopology J] [ProperSpace J]
    [MeasurableSpace J] [BorelSpace J] [MeasurableMul J]
    (e : MetricQuasiEquivalence P J) (hP : IsVirtuallyPolycyclic P)
    (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
    {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
    [SimplyConnectedSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))
    (u : MetricQuasiEquivalence J G)
    (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
    {I B₀ : Type*} [Fintype I] [Fintype B₀] [Nonempty B₀]
    (D : SupportDatum W I B₀)
    {L : ℝ≥0} (hπ : LipschitzWith L (fun g => (π g).toAdd))
    (c : ControlledContraction G)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ s) ≤ dist 1 g * |t - s|)
    (hheight : ∀ Λ : ℝ≥0, 2 ≤ (Λ : ℝ) →
      ∃ label : NormalizedPair G Λ → templateSymmetryGroup D,
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ p x, ‖(π (p.val.1 x)).toAdd - (label p).val (π x).toAdd‖ ≤ B) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨Λ, hΛ, Eclose, hEclose, rep, hrep, hclose, _⟩ :=
    u.exists_transferred_pair_representatives c hpath
  obtain ⟨label, B, hB, hbound⟩ := hheight Λ hΛ
  exact recognition_and_lattice_of_pair_representatives dekimpe liFP eaFP
    liPD bieri e hP hPfinite T W q π Exp hExp hπExp u gromov D hπ
    label hB hbound rep hrep hEclose hclose

end PolycyclicRecognition

end

end OAI
