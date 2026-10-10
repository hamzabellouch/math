import OAI.GroupTheory.PolycyclicRecognition.Finiteness.VirtualPolycyclicDuality
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RecognitionFromHeight
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseModelMean
import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeCharacterization
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricQuasiEquivalence
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricCoarseBridge

namespace OAI

/-!
# Recognition from bounded-height hypotheses

Metric comparison with the virtually polycyclic group supplies the invariant
mean and the cohomological coarse comparison.

The conditional recognition theorems retain polynomial bounded-height packing
and a uniform affine height estimate as explicit geometric hypotheses.
-/

noncomputable section

namespace PolycyclicRecognition

namespace MetricQuasiEquivalence

variable {P H : Type} [Group P] [Group H] [MetricSpace P] [MetricSpace H]
  [IsIsometricSMul P P] [IsIsometricSMul H H]

/-- Finite metric balls turn the specified coarse inverse maps into the
finite-difference comparison required by the cohomological inputs. -/
def groupCoarseEquivalence (e : MetricQuasiEquivalence P H)
    (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
    (hHfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite) :
    GroupCoarseEquivalence P H where
  toFun := e.toFun
  invFun := e.invFun
  bornologous_toFun := by
    obtain ⟨K, C, hK, _, hf⟩ := e.toFun_control
    exact groupBornologous_of_metric_bound e.toFun hHfinite hK hf
  bornologous_invFun := by
    obtain ⟨K, C, hK, _, hr⟩ := e.invFun_control
    exact groupBornologous_of_metric_bound e.invFun hPfinite hK hr
  left_error := by
    obtain ⟨E, _, hleft⟩ := e.left_close
    exact finite_groupDifference_range_of_metric_bound (e.invFun ∘ e.toFun) hPfinite hleft
  right_error := by
    obtain ⟨E, _, hright⟩ := e.right_close
    exact finite_groupDifference_range_of_metric_bound (e.toFun ∘ e.invFun) hHfinite hright

/-- Amenability is derived from the original comparison group and the
actual metric comparison, rather than assumed for the recognized group. -/
theorem invariantMean_of_virtuallyPolycyclic
    [DiscreteTopology H] [ProperSpace H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableMul H]
    (e : MetricQuasiEquivalence P H) (hP : IsVirtuallyPolycyclic P)
    (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite) :
    Nonempty (ThompsonNonamenability.InvariantMean H) := by
  classical
  obtain ⟨_, _, K', _, E, _, _, hK', _, hE, _, hlower, hsurj⟩ :=
    e.quasiIsometry_toFun
  exact invariantMean_of_coarse_virtualPolycyclic hP hPfinite e.toFun hE hK'
    hsurj hlower

/-- Once geometry has supplied elementary amenability, the actual metric
comparison supplies all comparison data in the published duality endgame. -/
theorem virtuallyPolycyclic_of_elementaryAmenable
    [Group.FG P] [Group.FG H]
    (liFP : LiFinitenessInput) (eaFP : ElementaryAmenableFinitenessInput)
    (liPD : LiDualityInput) (bieri : BieriDualityInput)
    (e : MetricQuasiEquivalence P H) (hP : IsVirtuallyPolycyclic P)
    (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
    (hHfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite)
    (hEA : IsElementaryAmenable H) : IsVirtuallyPolycyclic H :=
  virtuallyPolycyclic_of_elementaryAmenable_coarse_virtualPolycyclic_proved
    liFP eaFP liPD bieri P H hP
    (e.groupCoarseEquivalence hPfinite hHfinite) hEA

end MetricQuasiEquivalence

/-- The corrected height, including its possibly infinitely generated
kernel, gives both algebraic conclusions once its geometric packing bound is
available. No arbitrary Poincaré-duality comparison group is assumed. -/
theorem recognition_and_lattice_of_corrected_height
    (dekimpe : DekimpeLatticeRealizationInput)
    (liFP : LiFinitenessInput) (eaFP : ElementaryAmenableFinitenessInput)
    (liPD : LiDualityInput) (bieri : BieriDualityInput)
    {P H : Type} [Group P] [Group H] [MetricSpace P] [MetricSpace H]
    [IsIsometricSMul P P] [IsIsometricSMul H H] [Group.FG P] [Group.FG H]
    (e : MetricQuasiEquivalence P H) (hP : IsVirtuallyPolycyclic P)
    (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
    (hHfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite)
    {X W : Type} [PseudoMetricSpace X] [DecidableEq X] [NormedAddCommGroup W]
    (H₀ : Subgroup H) [H₀.FiniteIndex] (τ : H₀ →* Multiplicative W)
    (gromov : ∀ (J : Subgroup τ.ker) [DecidableEq J], GromovPolynomialGrowthInput J)
    (f : H → X) (π : X → W) (packing : PolynomialBoundedChainPacking π)
    {K C K' C' D : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hK' : 0 ≤ K') (hD : 0 ≤ D)
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hheight : ∀ h : H₀, ‖(τ h).toAdd - π (f h)‖ ≤ D) :
    IsVirtuallyPolycyclic H ∧
      ∃ Γ : Subgroup H, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  have hEA := elementaryAmenable_of_corrected_height H₀ τ gromov f π packing
    hHfinite hK hC hK' hD hupper hlower hheight
  have hH := e.virtuallyPolycyclic_of_elementaryAmenable liFP eaFP liPD bieri
    hP hPfinite hHfinite hEA
  exact ⟨hH, exists_uniform_solvable_lattice_of_virtuallyPolycyclic dekimpe H hH⟩

/-- The same conclusion directly from the affine-height interface. The
specified metric coarse inverses provide all transfer maps and estimates;
amenable correction, the height kernel, finiteness and duality are proved
in the invoked supporting theorems. The affine estimate and packing remain
the two explicit geometric obligations. -/
theorem recognition_and_lattice_of_affine_height
    (dekimpe : DekimpeLatticeRealizationInput)
    (liFP : LiFinitenessInput) (eaFP : ElementaryAmenableFinitenessInput)
    (liPD : LiDualityInput) (bieri : BieriDualityInput)
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
  have hEA := elementaryAmenable_of_transferred_height gromov u.toFun u.invFun π
    packing A hπsurj L K C E B K' C' hL hK hC hE hB hK' hπ hupper hlower
    (fun h => (dist_comm _ _).trans_le (hleft h)) haffine M hA hfinite
  have hH := e.virtuallyPolycyclic_of_elementaryAmenable liFP eaFP liPD bieri
    hP hPfinite hfinite hEA
  exact ⟨hH, exists_uniform_solvable_lattice_of_virtuallyPolycyclic dekimpe H hH⟩

end PolycyclicRecognition

end

end OAI
