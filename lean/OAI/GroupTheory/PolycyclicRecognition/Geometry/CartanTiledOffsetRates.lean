import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarTiledSamplers
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarOffsetExponents
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Matching the actual source partition count to the target exponent -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (K : ProperCone ℝ (StrongDual ℝ W))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]


local notation "C" => heightConePreimage T eW K

omit [SimplyConnectedSpace G] [Nonempty (Fin M.letterCount)]
    [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
/-- The stored tile count has exactly the source-minus-target exponent,
including when the transformed cone has a different ideal dimension. -/
theorem PolarTiledSamplerData.count_le_offset_rate
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    {ε : ℝ} (hε : 0 < ε) (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β)
    (R : ℝ) (scale : ℕ → ℝ) (φ : ℕ → I ≃ₜ* I)
    (D : M.PolarTiledSamplerData T F hunimod eW K ExpI ι bN ε β R scale φ)
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (bI' : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val)))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val))))
    (β' : M.ConeIdealBases (heightConePreimage T eW (transformedPolarCone K A.val)))
    (hβ' : M.IsMaximizingConeIdealBasis
      (heightConePreimage T eW (transformedPolarCone K A.val)) bI'
      ((M.supportIn T hunimod eW).weightSupport
        (A.val '' normalizedPolarTemplates K ε 2)) β') (n : ℕ) :
    (D.tiles n : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) * Real.exp (scale n *
      ((M.supportIn T hunimod eW).templateSupport (normalizedPolarTemplates K ε 0) -
        ∑ j, M.coneIdealWordCost
          (heightConePreimage T eW (transformedPolarCone K A.val))
          ((M.supportIn T hunimod eW).weightSupport
            (A.val '' normalizedPolarTemplates K ε 2)) (β'.val j))) := by
  have hb := M.polar_offset_exponent_balance T hunimod eW K A bN bI β hβ bI' β' hε hβ'
  change (M.supportIn T hunimod eW).templateSupport (normalizedPolarTemplates K ε 0) -
    (∑ j, M.coneIdealWordCost
      (heightConePreimage T eW (transformedPolarCone K A.val))
      ((M.supportIn T hunimod eW).weightSupport
        (A.val '' normalizedPolarTemplates K ε 2)) (β'.val j)) = _ at hb
  rw [hb]
  exact D.count n

end PolycyclicRecognition.CartanWordModel

end

end OAI
