import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntrinsicKernelPacking
import OAI.GroupTheory.PolycyclicRecognition.Lattices.RecognitionLatticeAssembly
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RecognitionInLieModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateSymmetries

namespace OAI

/-! # Recognition from affine control of canonical Lie height

A uniform affine-height estimate combines with polynomial bounded-height
packing and the comparison group's Poincare-duality data to give the
recognition conclusions.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold NNReal

/-- Canonical height supplies bounded-height packing for the two recognition
conclusions under a uniform affine-height estimate. -/
theorem recognition_and_lattice_of_canonical_affine_height
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
    [SimplyConnectedSpace G] [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))
    (u : MetricQuasiEquivalence J G)
    (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
    (A : J → W ≃L[ℝ] W) (hA : Set.Finite (Set.range A))
    {L : ℝ≥0} (hπ : LipschitzWith L (fun g => (π g).toAdd))
    {B : ℝ} (hB : 0 ≤ B)
    (haffine : ∀ h x,
      ‖(π (transferredMap u.toFun u.invFun h x)).toAdd -
        ((π (u.toFun h)).toAdd + A h (π x).toAdd)‖ ≤ B) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  have hsurj : Function.Surjective (fun g => (π g).toAdd) := by
    intro w
    obtain ⟨g, hg⟩ := integrated_height_surjective T q Exp π hπExp (Multiplicative.ofAdd w)
    exact ⟨g, congrArg Multiplicative.toAdd hg⟩
  exact recognition_and_lattice_of_affine_height dekimpe liFP eaFP liPD bieri
    e hP hPfinite u (fun g => (π g).toAdd)
    (polynomialBoundedChainPacking_intrinsic T Exp hExp q π hπExp)
    gromov A hA hsurj L.coe_nonneg hB (fun x y => by
      simpa only [dist_eq_norm] using hπ.dist_le_mul x y) haffine

/-- The geometric theorem's template symmetry labels have finite image
by the proved support-polytope argument. This removes the separate finite
image premise from the finiteness and duality endgame. -/
theorem recognition_and_lattice_of_template_affine_height
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
    [SimplyConnectedSpace G] [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))
    (u : MetricQuasiEquivalence J G)
    (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
    {I B₀ : Type*} [Fintype I] [Fintype B₀] [Nonempty B₀]
    (D : SupportDatum W I B₀) (A : J → templateSymmetryGroup D)
    {L : ℝ≥0} (hπ : LipschitzWith L (fun g => (π g).toAdd))
    {B : ℝ} (hB : 0 ≤ B)
    (haffine : ∀ h x,
      ‖(π (transferredMap u.toFun u.invFun h x)).toAdd -
        ((π (u.toFun h)).toAdd + (A h).val (π x).toAdd)‖ ≤ B) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  let Ac : J → W ≃L[ℝ] W := fun h => (A h).val.toContinuousLinearEquiv
  have hAc : Set.Finite (Set.range Ac) := by
    apply (Set.finite_range (fun f : templateSymmetryGroup D =>
      f.val.toContinuousLinearEquiv)).subset
    rintro _ ⟨h, rfl⟩
    exact ⟨A h, rfl⟩
  exact recognition_and_lattice_of_canonical_affine_height dekimpe liFP eaFP
    liPD bieri e hP hPfinite T W q π Exp hExp hπExp u gromov
    Ac hAc hπ hB haffine

end PolycyclicRecognition

end

end OAI
