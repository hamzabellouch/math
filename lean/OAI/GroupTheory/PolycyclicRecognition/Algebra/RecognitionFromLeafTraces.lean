import OAI.GroupTheory.PolycyclicRecognition.Analysis.RecognitionFromCanonicalAffine
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundedHeightEndgame

namespace OAI

/-! # The leaf and boundary-trace estimates feed both recognition conclusions -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold NNReal

/-- The actual transferred maps need not use an inverse normalized at the
identity. Its fixed basepoint error is uniformly bounded by the coarse map
and height controls. The geometric leaf and trace estimates then supply
both finiteness/duality recognition conclusions. -/
theorem recognition_and_lattice_of_leaf_and_traces
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
    {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)} [H.IsCartanSubalgebra]
    (F : CartanFactorModel H Exp) (hbijN : Function.Bijective F.ExpN)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (u : MetricQuasiEquivalence J G)
    (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
    {I B₀ : Type*} [Fintype I] [Fintype B₀] [Nonempty B₀]
    (D : SupportDatum W I B₀) (A : J → templateSymmetryGroup D)
    {L : ℝ≥0} (hπ : LipschitzWith L (fun g => (π g).toAdd))
    {K : Type*} [Fintype K] (α β : K → Module.Dual ℝ W)
    (hsep : ∀ w, (∀ i, β i w = 0) → w = 0)
    (hsub : ∀ h ε, 0 < ε → ∃ B : ℝ, ∀ g,
      ‖(π (transferredMap u.toFun u.invFun h g)).toAdd -
        (π (transferredMap u.toFun u.invFun h 1)).toAdd -
        (A h).val (π g).toAdd‖ ≤ ε * dist 1 g + B)
    {Lleaf Btrace : ℝ} (hLleaf : 0 ≤ Lleaf) (hBtrace : 0 ≤ Btrace)
    (hleaf : ∀ h x n,
      ‖(π (transferredMap u.toFun u.invFun h (x * F.inclusionN n))).toAdd -
        (π (transferredMap u.toFun u.invFun h x)).toAdd‖ ≤ Lleaf)
    (htrace : ∀ h d i,
      |β i ((π (transferredMap u.toFun u.invFun h (F.inclusionD d))).toAdd -
          (π (transferredMap u.toFun u.invFun h 1)).toAdd) -
        α i (π (F.inclusionD d)).toAdd| ≤ Btrace) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  let η := fun h g => (π (transferredMap u.toFun u.invFun h g)).toAdd
  obtain ⟨_, B, hB, hbound⟩ := F.uniform_affine_bound_of_leaf_and_averaged_traces
    T q π hπExp hbijN chartD hchartD α β hsep η
    (fun h => (A h).val.toLinearMap) hsub hLleaf hBtrace hleaf htrace
  obtain ⟨K, C, hK, hC, hu⟩ := u.toFun_control
  let Cbase := (L : ℝ) * (K * dist (u.invFun 1) 1 + C)
  have hCbase : 0 ≤ Cbase :=
    mul_nonneg L.coe_nonneg (add_nonneg (mul_nonneg hK dist_nonneg) hC)
  have hbase (h : J) : ‖η h 1 - (π (u.toFun h)).toAdd‖ ≤ Cbase := by
    have hd : dist (u.toFun (h * u.invFun 1)) (u.toFun h) ≤
        K * dist (u.invFun 1) 1 + C := by
      have hcontrol := hu (h * u.invFun 1) (h * 1)
      rw [dist_mul_left] at hcontrol
      simpa only [mul_one] using hcontrol
    exact (show ‖η h 1 - (π (u.toFun h)).toAdd‖ ≤
      (L : ℝ) * dist (u.toFun (h * u.invFun 1)) (u.toFun h) by
        simpa only [η, transferredMap, dist_eq_norm] using
          hπ.dist_le_mul (u.toFun (h * u.invFun 1)) (u.toFun h)).trans
      (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
  apply recognition_and_lattice_of_template_affine_height dekimpe liFP eaFP
    liPD bieri e hP hPfinite T W q π Exp hExp hπExp u gromov D A hπ
    (add_nonneg hB hCbase)
  intro h x
  calc
    _ = ‖(η h x - (η h 1 + (A h).val (π x).toAdd)) +
        (η h 1 - (π (u.toFun h)).toAdd)‖ := by
      change ‖η h x - _‖ = _
      congr 1
      abel
    _ ≤ ‖η h x - (η h 1 + (A h).val (π x).toAdd)‖ +
        ‖η h 1 - (π (u.toFun h)).toAdd‖ := norm_add_le _ _
    _ ≤ B + Cbase := add_le_add (hbound h x) (hbase h)

end PolycyclicRecognition

end

end OAI
