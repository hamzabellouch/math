import OAI.GroupTheory.PolycyclicRecognition.Finiteness.VirtualPolycyclicDuality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RecognitionFromPolycyclicComparison
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseModelMean

namespace OAI

/-! # Recognition from affine height control

An invariant mean, finite-index corrected height and Poincaré-duality
comparison turn an affine height bound into a recognition conclusion.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

theorem virtuallyPolycyclic_of_affine_height_coarse_virtualPolycyclic
    (liFP : LiFinitenessInput) (eaFP : ElementaryAmenableFinitenessInput)
    (liPD : LiDualityInput) (bieri : BieriDualityInput)
    {P H : Type} [Group P] [MetricSpace P] [IsIsometricSMul P P]
    [Group H] [MetricSpace H] [DiscreteTopology H] [ProperSpace H]
    [IsIsometricSMul H H] [MeasurableSpace H] [BorelSpace H] [MeasurableMul H]
    [Group.FG P] [Group.FG H]
    (hP : IsVirtuallyPolycyclic P) (e : GroupCoarseEquivalence P H)
    (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
    (u : P → H) {c₀ K₀ C₀ : ℝ} (hc₀ : 0 ≤ c₀) (hK₀ : 0 ≤ K₀)
    (husurj : ∀ y, ∃ p, dist y (u p) ≤ c₀)
    (hulower : ∀ x y, dist x y ≤ K₀ * dist (u x) (u y) + C₀)
    {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
    [SimplyConnectedSpace G] [IsIsometricSMul G G] [ProperSpace G]
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (π : G →* Multiplicative W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))
    (dixmier : DixmierExponentialInput (E := E) (G := G))
    (realize : OnshuusPostRealizationInput T)
    (gromov : ∀ (J : Type) [Group J] [DecidableEq J], GromovPolynomialGrowthInput J)
    (f : H → G) (r : G → H) (A : H → W ≃L[ℝ] W)
    (hπsurj : Function.Surjective (fun g => (π g).toAdd))
    (L K C E₀ B K' C' : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B) (hK' : 0 ≤ K')
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ L * dist x y)
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hrf : ∀ h, dist (r (f h)) h ≤ E₀)
    (haffine : ∀ h x,
      ‖(π (transferredMap f r h x)).toAdd - ((π (f h)).toAdd + A h (π x).toAdd)‖ ≤ B)
    (hA : Set.Finite (Set.range A)) : IsVirtuallyPolycyclic H := by
  classical
  obtain ⟨M⟩ := invariantMean_of_coarse_virtualPolycyclic hP hPfinite u hc₀ hK₀
    husurj hulower
  have hpacking := polynomialBoundedChainPacking_of_published_realization T
    dixmier realize Exp hExp q π hπExp
  have hEA := elementaryAmenable_of_transferred_height gromov f r
    (fun g => (π g).toAdd) hpacking A hπsurj L K C E₀ B K' C'
    hL hK hC hE₀ hB hK' hπ hupper hlower hrf haffine M hA
    (fun R => (isCompact_closedBall (1 : H) R).finite_of_discrete)
  exact virtuallyPolycyclic_of_elementaryAmenable_coarse_virtualPolycyclic_proved
    liFP eaFP liPD bieri P H hP e hEA

end PolycyclicRecognition

end

end OAI
