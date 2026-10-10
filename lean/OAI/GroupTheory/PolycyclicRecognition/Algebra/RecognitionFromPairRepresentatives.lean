import OAI.GroupTheory.PolycyclicRecognition.Analysis.RecognitionFromCanonicalAffine
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NormalizedPairHeightTransfer

namespace OAI

/-! # The finiteness and duality endgame for bounded pair representatives -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold NNReal

/-- This bridge applies the proved normalized height estimate to actual
transferred maps once their uniformly close Lipschitz representatives are
constructed. Representative existence remains a separate obligation. -/
theorem recognition_and_lattice_of_pair_representatives
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
    {Λ : ℝ≥0} (label : NormalizedPair G Λ → templateSymmetryGroup D)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ p x, ‖(π (p.val.1 x)).toAdd - (label p).val (π x).toAdd‖ ≤ B)
    (rep : J → C(G, G) × C(G, G)) (hrep : ∀ h, LipschitzPairBounds G Λ (rep h))
    {Eclose : ℝ} (hEclose : 0 ≤ Eclose)
    (hclose : ∀ h x, dist ((rep h).1 x) (transferredMap u.toFun u.invFun h x) ≤ Eclose) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨A, K, hK, hc⟩ := uniform_affine_height_of_bounded_pair_representatives
    D π L.coe_nonneg
    (fun x y => by simpa only [dist_eq_norm] using hπ.dist_le_mul x y)
    label hB hbound (transferredMap u.toFun u.invFun) rep hrep hEclose hclose
  obtain ⟨Ku, Cu, hKu, hCu, hu⟩ := u.toFun_control
  let Cbase := (L : ℝ) * (Ku * dist (u.invFun 1) 1 + Cu)
  have hCbase : 0 ≤ Cbase :=
    mul_nonneg L.coe_nonneg (add_nonneg (mul_nonneg hKu dist_nonneg) hCu)
  have hbase (h : J) :
      ‖(π (transferredMap u.toFun u.invFun h 1)).toAdd - (π (u.toFun h)).toAdd‖ ≤ Cbase := by
    have hd : dist (u.toFun (h * u.invFun 1)) (u.toFun h) ≤
        Ku * dist (u.invFun 1) 1 + Cu := by
      have hcontrol := hu (h * u.invFun 1) (h * 1)
      rw [dist_mul_left] at hcontrol
      simpa only [mul_one] using hcontrol
    exact (show ‖(π (transferredMap u.toFun u.invFun h 1)).toAdd - (π (u.toFun h)).toAdd‖ ≤
        (L : ℝ) * dist (u.toFun (h * u.invFun 1)) (u.toFun h) by
      simpa only [transferredMap, dist_eq_norm] using
        hπ.dist_le_mul (u.toFun (h * u.invFun 1)) (u.toFun h)).trans
      (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
  apply recognition_and_lattice_of_template_affine_height dekimpe liFP eaFP
    liPD bieri e hP hPfinite T W q π Exp hExp hπExp u gromov D A hπ
    (add_nonneg hK hCbase)
  intro h x
  calc
    _ = ‖((π (transferredMap u.toFun u.invFun h x)).toAdd -
          ((π (transferredMap u.toFun u.invFun h 1)).toAdd + (A h).val (π x).toAdd)) +
        ((π (transferredMap u.toFun u.invFun h 1)).toAdd - (π (u.toFun h)).toAdd)‖ := by
      congr 1
      abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ K + Cbase := add_le_add (hc h x) (hbase h)

end PolycyclicRecognition

end

end OAI
