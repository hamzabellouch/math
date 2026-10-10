import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanStationaryTemplateComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPathPacking
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSegmentExponent
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateThickeningLimit
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PathVolumeComparison

namespace OAI

/-! # Actual stationary template-volume comparison

The lower count uses independently sampled coordinates of the actual root
factor. The upper count uses the image paths in the ambient group. No
volume-comparison statement is assumed as an input.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal Pointwise

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

include hπExp hchartN hchartD dynkinN dynkinD haarN haarD in
theorem templateSupport_le_of_stationary_height_factor
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hΛ : 0 < (Λ : ℝ)) {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (A : W →L[ℝ] W) (hA : ∀ g, (l g).toAdd = A (π g).toAdd)
    (C : Set W) (hC : IsCompact C) (hconv : Convex ℝ C) (hC0 : (0 : W) ∈ C) :
    (M.supportIn T hunimod eW).templateSupport C ≤
      (M.supportIn T hunimod eW).templateSupport (A '' C) := by
  classical
  let P := M.supportIn T hunimod eW
  have hsurj : ∀ w : W, ∃ v : H, (π (Exp v)).toAdd = w := by
    intro w
    obtain ⟨v, hv⟩ := (eW.surjective.comp (cartan_height_surjective T H)) w
    exact ⟨v, (hπExp v).trans hv⟩
  choose w hw hsupport using fun i => P.exists_weightSupport_point hC ⟨0, hC0⟩ i
  choose v hv using fun i => hsurj (w i)
  have hweight (i : Fin M.letterCount) : M.weight i (v i) = P.weightSupport C i := by
    rw [hsupport i, ← hv i, hπExp]
    change M.weight i (v i) = cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (v i))))
    rw [eW.symm_apply_apply, cartanHeightWeight_projection]
  have hvA (i : Fin M.letterCount) : (l (Exp (v i))).toAdd ∈ A '' C := by
    rw [hA, hv i]
    exact mem_image_of_mem A (hw i)
  obtain ⟨β, hβ, hle⟩ := M.exists_template_exponent_le_of_stationary_mean
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD
    hExp realize μ l hπ hl hΛ hK hL hLip hbound hsub b₀ hφ hpath v (A '' C)
    (hC.image A.continuous) (hconv.linear_image A.toLinearMap)
    (by simpa using mem_image_of_mem A hC0) hvA
  have hcost : (fun w : M.wordList => bracketWordExponent (M.templateSupportExponent v) w) =
      M.boxCost T hunimod eW C := by
    funext w
    exact congrArg (fun s => bracketWordExponent s w) (funext hweight)
  rw [hcost] at hβ hle
  rwa [M.columnBasisWeight_eq_templateSupport_of_maximizing T hunimod eW b₀ C β hβ] at hle

end PolycyclicRecognition.CartanWordModel

end

end OAI
