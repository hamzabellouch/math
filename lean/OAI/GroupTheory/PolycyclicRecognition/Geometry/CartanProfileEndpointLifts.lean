import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanPathLifts
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateBoxEnvelopes
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ControlledPathErrorEnvelope

namespace OAI

/-! # Common factor boxes for families of controlled paths

Vanishing height errors are absorbed in one fixed maximizing basis. The
endpoint and its compact right thickening share the same chosen factor lift.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter
open scoped Manifold Pointwise Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)

include hπExp hchartN hchartD dynkinN dynkinD in
/-- An unthickened endpoint lift retains the exact endpoint height and its
common subexponential boxes. This choice is made before the short bridge. -/
theorem exists_sequence_profile_endpoint_lifts
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale η : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale1 : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n)
    (hη : Tendsto η atTop (𝓝 0))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ RN RD : ℕ → ℝ, (∀ n, 0 ≤ RN n) ∧ (∀ n, 0 ≤ RD n) ∧
      HasSubexponentialUpperBoundSeq scale RN ∧ HasSubexponentialUpperBoundSeq scale RD ∧
      ∀ n {g : G} (γ : Path (1 : G) g),
        PathMetricBound γ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
        (∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - scale n • z‖ ≤
          2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
        ∃ (u : F.N.carrier) (d : F.D.carrier),
          F.inclusionN u * F.inclusionD d = g ∧
          (π (F.inclusionD d)).toAdd = (π g).toAdd ∧
          u ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
            E β (scale n) (RN n) ∧
          ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
            (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective)
            d)‖ ≤ RD n := by
  obtain ⟨RN, RD, hRN0, hRD0, hRN, hRD, hlift⟩ :=
    M.exists_sequence_controlled_profile_lifts T F hunimod eW π hπExp
      chartN hchartN chartD hchartD dynkinN dynkinD b₀ γ₀
      (isCompact_singleton (x := ((1 : F.N.carrier), (1 : F.D.carrier))))
      hφ hpath hK hLip hE hne β hβ scale η hscale hscale1 hη0 hη A B hA hB
  refine ⟨RN, RD, hRN0, hRD0, hRN, hRD, ?_⟩
  intro n g path hmetric hheight
  obtain ⟨u, d, hprod, hdheight, hthick⟩ := hlift n path hmetric hheight
  have hb := hthick (1, 1) (Set.mem_singleton (1, 1))
  refine ⟨u, d, hprod, hdheight, ?_, ?_⟩
  · simpa only [map_one, mul_one] using hb.1
  · simpa only [mul_one] using hb.2

end PolycyclicRecognition.CartanWordModel

end

end OAI
