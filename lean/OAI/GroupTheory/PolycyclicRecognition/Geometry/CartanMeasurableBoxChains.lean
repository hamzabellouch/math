import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMeasurableGeneratorChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTemplateSupports

namespace OAI

/-! # Borel generator chains for the actual compact probe templates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric
open scoped Manifold

variable {EG G W A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [MeasurableSpace A]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The compact template supplies its own support directions. Every Borel
sampler in its coordinate box then has a fixed-length generator chain,
with measurable prefixes and uniform bounds in a dominating box. -/
theorem exists_measurable_box_generator_chain
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (N : ℕ) (C D : ℝ), 1 ≤ C ∧ 0 ≤ D ∧
      ∀ r : ℝ, 0 ≤ r → ∀ (β γ : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ t : Fin M.letterCount → ℝ,
      (∀ i, (M.supportIn T hunimod eW).weightSupport E i ≤ t i) →
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent t w) γ.val →
      ∀ y : A → closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R,
        Measurable y →
      ∃ (mode : Fin N → Fin M.letterCount) (coeff : A → Fin N → ℝ)
        (vertex : A → Fin (N + 1) → cartanRootIdeal H),
        (∀ j, Measurable (fun q => coeff q j)) ∧
        (∀ j, Measurable (fun q => b₀.equivFun (vertex q j))) ∧
        (∀ q j, |coeff q j| ≤ C * Real.exp (r *
          (M.supportIn T hunimod eW).weightSupport E (mode j))) ∧
        (∀ q, vertex q 0 = 0) ∧
        (∀ q, vertex q (Fin.last N) = (M.boxBasis T hunimod eW E β r).equivFun.symm (y q).val) ∧
        (∀ q j, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
          (fun k => bracketWordExponent t (γ.val k)) r).equivFun (vertex q j)‖ ≤ D) ∧
        ∀ q j, F.ExpN (F.N.equiv (vertex q j.succ)) =
          F.ExpN (F.N.equiv (vertex q j.castSucc)) *
            F.ExpN (F.N.equiv (coeff q j • M.letter (mode j))) := by
  obtain ⟨v, _, hv⟩ := M.exists_cartan_template_supports T hunimod eW E hE hne
  obtain ⟨N, C, D, hC, hD, hchain⟩ := M.exists_measurable_template_generator_chain (A := A) T F
    hExp realize haarN dynkinN b₀ v R hR
  refine ⟨N, C, D, hC, hD, ?_⟩
  intro r hr β γ hβ t hst hγ y hy
  have hβ' : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent (M.templateSupportExponent v) w) β.val := by
    change IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent ((M.supportIn T hunimod eW).weightSupport E) w) β.val at hβ
    simpa only [hv] using hβ
  have hst' : ∀ i, M.templateSupportExponent v i ≤ t i := by simpa only [hv] using hst
  have hh := hchain r hr β γ hβ' t hst' hγ y hy
  simpa only [hv, CartanWordModel.boxBasis, CartanWordModel.boxCost] using hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
