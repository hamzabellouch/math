import OAI.GroupTheory.PolycyclicRecognition.Geometry.RecognitionInLieModel
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.VirtualPolycyclicDuality

namespace OAI

/-! # The geometric height estimate feeds the original polycyclic comparison

This composition removes the separate Poincaré-duality comparison premise.
The corrected height estimate remains a geometric obligation; this theorem
is not the manuscript's completed recognition theorem.
-/

namespace PolycyclicRecognition

open scoped Manifold

variable {H : Type} [Group H] [MetricSpace H] [IsIsometricSMul H H]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [SimplyConnectedSpace G] [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (q : HeightSpace T.character ≃ₗ[ℝ] W)
  (π : G →* Multiplicative W)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))

include hExp hπExp in
theorem virtuallyPolycyclic_of_corrected_height_coarse_virtualPolycyclic
    (liFP : LiFinitenessInput) (eaFP : ElementaryAmenableFinitenessInput)
    (liPD : LiDualityInput) (bieri : BieriDualityInput)
    (dixmier : DixmierExponentialInput (E := E) (G := G))
    (realize : OnshuusPostRealizationInput T)
    (P : Type) [Group P] [Group.FG P] [Group.FG H]
    (hP : IsVirtuallyPolycyclic P) (e : GroupCoarseEquivalence P H)
    (H₀ : Subgroup H) [H₀.FiniteIndex] (τ : H₀ →* Multiplicative W)
    (gromov : ∀ (J : Subgroup τ.ker) [DecidableEq J], GromovPolynomialGrowthInput J)
    (f : H → G) (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite)
    {K C K' C' D : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hK' : 0 ≤ K') (hD : 0 ≤ D)
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hheight : ∀ h : H₀, ‖(τ h).toAdd - (π (f h)).toAdd‖ ≤ D) :
    IsVirtuallyPolycyclic H := by
  have hEA := elementaryAmenable_of_corrected_canonical_height T q π Exp hExp hπExp
    dixmier realize H₀ τ gromov f hfinite hK hC hK' hD hupper hlower hheight
  exact virtuallyPolycyclic_of_elementaryAmenable_coarse_virtualPolycyclic_proved
    liFP eaFP liPD bieri P H hP e hEA

end PolycyclicRecognition

end OAI
