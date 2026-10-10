import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundedTemplatePaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTemplateSupports
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGroupBoxes

namespace OAI

/-! # Controlled paths for the actual compact-template Cartan boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)


variable
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Every point of a fixed-radius logarithmic box has a continuously
selected path of linear coarse length through the prescribed height template.
Supporting directions and their exact exponents are constructed. -/
theorem exists_continuous_compact_template_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(π g).toAdd‖ ≤ L * dist 1 g)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (hE : IsCompact E) (hconv : Convex ℝ E) (hE0 : (0 : W) ∈ E)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∃ γ : ∀ y : closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R,
          Path (1 : G) (F.inclusionN (F.ExpN (F.N.equiv
            ((M.boxBasis T hunimod eW E β r).equivFun.symm y.val)))),
        (∀ t, Continuous (fun y => γ y t)) ∧
        (∀ y, PathMetricBound (γ y) (C * r) (C * (1 + Real.log (2 + r)))) ∧
        ∀ y t, ∃ z ∈ E, (π (γ y t)).toAdd = r • z := by
  obtain ⟨v, hv, hs⟩ := M.exists_cartan_template_supports T hunimod eW E hE ⟨0, hE0⟩
  have hvπ (i) : (π (Exp (v i))).toAdd ∈ E := by
    rw [hπExp]
    exact hv i
  have hpaths := M.exists_continuous_bounded_template_paths T F hExp realize haarN dynkinN
    π hπ hL hbound b₀ v E hconv hE0 hvπ R hR
  obtain ⟨C, hC, hp⟩ := hpaths
  refine ⟨C, hC, ?_⟩
  intro r hr β hβ
  change IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
    (fun w : M.wordList => bracketWordExponent
      ((M.supportIn T hunimod eW).weightSupport E) w) β.val at hβ
  have hβ' : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent (M.templateSupportExponent v) w) β.val := by
    simpa only [hs] using hβ
  have hh := hp r hr β hβ'
  dsimp only at hh
  have hb : exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
      (fun j => bracketWordExponent (M.templateSupportExponent v) (β.val j)) r =
        M.boxBasis T hunimod eW E β r := by
    rw [hs]
    rfl
  rw [hb] at hh
  exact hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
