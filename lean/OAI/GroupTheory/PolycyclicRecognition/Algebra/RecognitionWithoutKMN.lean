import OAI.GroupTheory.PolycyclicRecognition.Geometry.CorrectedHeightRecognition
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RecognitionFromUniformHeight

namespace OAI

/-! # The geometric recognition assembly without the KMN hypothesis

Rational dimension, bounded finite subgroup orders, and duality after removing
a finite normal subgroup give recognition with polynomial-growth recognition
as an explicit hypothesis.
-/
noncomputable section
namespace PolycyclicRecognition
open Set
open scoped Manifold NNReal

theorem recognition_and_lattice_of_affine_height_proved
    (dekimpe : DekimpeLatticeRealizationInput)
    {P H : Type} [Group P] [Group H] [MetricSpace P] [MetricSpace H]
    [IsIsometricSMul P P] [IsIsometricSMul H H] [Group.FG P] [Group.FG H]
    [DiscreteTopology H] [ProperSpace H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableMul H]
    (e : MetricQuasiEquivalence P H) (hP : IsVirtuallyPolycyclic P)
    (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
    {X W : Type} [PseudoMetricSpace X] [DecidableEq X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (u : MetricQuasiEquivalence H X) (π : X → W)
    (packing : PolynomialBoundedChainPacking π)
    (gromov : ∀ (J : Type) [Group J] [DecidableEq J], GromovPolynomialGrowthInput J)
    (A : H → W ≃L[ℝ] W) (hA : Set.Finite (Set.range A))
    (hπsurj : Function.Surjective π)
    {L B : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hπ : ∀ x y, ‖π x - π y‖ ≤ L * dist x y)
    (haffine : ∀ h x,
      ‖π (transferredMap u.toFun u.invFun h x) -
        (π (u.toFun h) + A h (π x))‖ ≤ B) :
    IsVirtuallyPolycyclic H ∧
      ∃ Γ : Subgroup H, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  classical
  obtain ⟨M⟩ := e.invariantMean_of_virtuallyPolycyclic hP hPfinite
  obtain ⟨K, C, K', C', _, hK, hC, hK', _, _, hupper, hlower, _⟩ :=
    u.quasiIsometry_toFun
  obtain ⟨E, hE, hleft⟩ := u.left_close
  have hfinite (R : ℝ) : (Metric.closedBall (1 : H) R).Finite :=
    (isCompact_closedBall (1 : H) R).finite_of_discrete
  obtain ⟨H₀, _, hindex, τ, D, hD, hheight, _⟩ :=
    TransferredHeight.exists_normal_finiteIndex_height u.toFun u.invFun π A hπsurj
      (fun h a b => dist_mul_left h a b) L K C E B hL hK hC hE hB hπ hupper
      (fun h => (dist_comm _ _).trans_le (hleft h)) haffine M hA
  let := hindex
  have hH := virtuallyPolycyclic_of_corrected_height_proved
    (e.groupCoarseEquivalence hPfinite hfinite) hP M H₀ τ (fun J => gromov J)
    u.toFun π packing hfinite hK hC hK' hD hupper hlower hheight
  exact ⟨hH, exists_uniform_solvable_lattice_of_virtuallyPolycyclic dekimpe H hH⟩

theorem recognition_and_lattice_of_canonical_affine_height_proved
    (dekimpe : DekimpeLatticeRealizationInput)
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
  exact recognition_and_lattice_of_affine_height_proved dekimpe
    e hP hPfinite u (fun g => (π g).toAdd)
    (polynomialBoundedChainPacking_intrinsic T Exp hExp q π hπExp)
    gromov A hA hsurj L.coe_nonneg hB (fun x y => by
      simpa only [dist_eq_norm] using hπ.dist_le_mul x y) haffine

theorem recognition_and_lattice_of_template_affine_height_proved
    (dekimpe : DekimpeLatticeRealizationInput)
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
  exact recognition_and_lattice_of_canonical_affine_height_proved dekimpe e hP hPfinite T W q π Exp hExp hπExp u gromov
    Ac hAc hπ hB haffine

theorem recognition_and_lattice_of_pair_representatives_proved
    (dekimpe : DekimpeLatticeRealizationInput)
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
  apply recognition_and_lattice_of_template_affine_height_proved dekimpe e hP hPfinite T W q π Exp hExp hπExp u gromov D A hπ
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

theorem recognition_and_lattice_of_uniform_normalized_height_proved
    (dekimpe : DekimpeLatticeRealizationInput)
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
  exact recognition_and_lattice_of_pair_representatives_proved dekimpe e hP hPfinite T W q π Exp hExp hπExp u gromov D hπ
    label hB hbound rep hrep hEclose hclose

end PolycyclicRecognition

end

end OAI
