import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularRealizationInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RecognitionFromHeight

namespace OAI

/-! # Finiteness and duality in a concrete Lie model

Canonical-height packing, a corrected height estimate and an integral
Poincaré-duality comparison imply virtual polycyclicity.
-/

noncomputable section

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

include hExp hπExp

/-- Corrected canonical height in the actual Lie group implies elementary
amenability, using published realization and Gromov inputs only for packing. -/
theorem elementaryAmenable_of_corrected_canonical_height
    (dixmier : DixmierExponentialInput (E := E) (G := G))
    (realize : OnshuusPostRealizationInput T)
    (H₀ : Subgroup H) [H₀.FiniteIndex] (τ : H₀ →* Multiplicative W)
    (gromov : ∀ (J : Subgroup τ.ker) [DecidableEq J], GromovPolynomialGrowthInput J)
    (f : H → G) (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite)
    {K C K' C' D : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hK' : 0 ≤ K') (hD : 0 ≤ D)
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hheight : ∀ h : H₀, ‖(τ h).toAdd - (π (f h)).toAdd‖ ≤ D) :
    IsElementaryAmenable H := by
  exact elementaryAmenable_of_corrected_height H₀ τ gromov f (fun g => (π g).toAdd)
    (polynomialBoundedChainPacking_of_published_realization T dixmier realize Exp hExp q π hπExp)
    hfinite hK hC hK' hD hupper hlower hheight

/-- The Lie-model growth estimate combines with the finiteness and duality
theorems under geometric height and comparison-model hypotheses. -/
theorem virtuallyPolycyclic_of_corrected_canonical_height
    (liFP : LiFinitenessInput) (eaFP : ElementaryAmenableFinitenessInput)
    (liPD : LiDualityInput) (bieri : BieriDualityInput)
    (dixmier : DixmierExponentialInput (E := E) (G := G))
    (realize : OnshuusPostRealizationInput T)
    (Γ : Type) [Group Γ] [Group.FG Γ] [Group.FG H]
    (e : GroupCoarseEquivalence Γ H)
    (d : ℕ) (hΓPD : IsIntegralPoincareDualityGroup Γ d)
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
  exact virtuallyPolycyclic_of_elementaryAmenable_coarse_PD liFP eaFP liPD bieri Γ H e hEA d hΓPD

end PolycyclicRecognition

end

end OAI
