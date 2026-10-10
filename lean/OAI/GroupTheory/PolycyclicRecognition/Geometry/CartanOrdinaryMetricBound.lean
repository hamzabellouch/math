import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProfileAnchors
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformSuffixMetric
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxScaling
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialRate
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExponentBounds

namespace OAI

/-! # Uniform metric bounds for the ordinary Haar cells -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

include T in
/-- The unit-radius ordinary cells have normalized diameter bounded at
all physical scales at least one. A constant scale sequence removes the
eventual quantifier from the suffix metric estimate. -/
theorem exists_ordinary_cell_metric_bound
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
      ∀ q ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1,
        dist 1 (F.inclusionN q) / r ≤ C := by
  obtain ⟨C, hC, hmetric⟩ := M.exists_uniform_suffix_metric_bound T F hunimod eW
    hExp realize haarN dynkinN b₀ hE hne hweights β hβ
  refine ⟨C, hC, ?_⟩
  intro r hr q hq
  have hR : HasSubexponentialUpperBoundSeq (fun _ : ℕ => r) (fun _ => 0) :=
    fun ε _ => Eventually.of_forall (fun _ => (Real.exp_pos (ε * r)).le)
  obtain ⟨n, hn⟩ := (hmetric 0 le_rfl zero_le_one (fun _ => r) (fun _ => 0)
    (fun _ => hr) hR).exists
  have hk : (1 : F.N.carrier) ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + (0 : ℝ)) • w) '' E) β r 0 :=
    ⟨0, by simp [F.isExpN.map_zero], by simp⟩
  exact hn 1 hk q ⟨q, hq, mul_one q⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
