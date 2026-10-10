import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanAlternatingLimit
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxSchemes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BundleWordCoordinates

namespace OAI

/-! # Simultaneous source and target polynomial schemes

The alternating length and the source word are selected from the actual
normalized Cartan laws before any good profile sets are imposed.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Filter Set
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

theorem exists_source_target_comparison_schemes
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (b : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {c : ℕ} (aN : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (E E₁ E₂ : Set W) (hE₁ : IsCompact E₁) (hne₁ : E₁.Nonempty)
    (hE₂ : IsCompact E₂) (hne₂ : E₂.Nonempty)
    (β β₁ β₂ γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW (E₁ ∪ E₂)) β.val)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW E₂) β₂.val)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW E) γ.val)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 ≤ scale n)
    (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H)) :
    ∃ u : ℕ → ℕ, StrictMono u ∧ ∃ h : ℕ, 0 < h ∧
      ∃ (target : AlternatingLawData (finrank ℝ (cartanRootIdeal H)))
        (z₀ : Fin h → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ×
          (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)),
        Tendsto (fun n =>
          let bU := M.boxBasis T hunimod eW (E₁ ∪ E₂) β (scale (u n))
          let b₁ := M.boxBasis T hunimod eW E₁ β₁ (scale (u n))
          let b₂ := M.boxBasis T hunimod eW E₂ β₂ (scale (u n))
          (basisBracket bU, boxCoordinateChange bU b₁, boxCoordinateChange bU b₂))
          atTop (𝓝 target) ∧
        Function.Surjective (fderiv ℝ
          (alternatingCoordinateProduct aN target.1 target.2.1 target.2.2) z₀) ∧
        ∃ (m : ℕ) (letters : Fin m → Fin M.letterCount)
          (source : WordLawData (Fin M.letterCount) (finrank ℝ (cartanRootIdeal H)))
          (t₀ : Fin (m + m) → ℝ),
          Tendsto (fun n =>
            let bS := M.boxBasis T hunimod eW E γ (scale (u n))
            (basisBracket bS, fun i => bS.equivFun
              (Real.exp (scale (u n) * (M.supportIn T hunimod eW).weightSupport E i) • M.letter i)))
            atTop (𝓝 source) ∧
          Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters source) t₀) := by
  obtain ⟨u, hu, h, hh, target, z₀, ht, htsub⟩ := M.exists_alternating_box_limit
    T F hunimod eW hExp realize haarN b aN hm E₁ E₂ hE₁ hne₁ hE₂ hne₂
    β β₁ β₂ hβ hβ₁ hβ₂ scale hscale hdim
  obtain ⟨C, _, source, _, v, hv, hs, m, letters, t₀, _, hssub⟩ :=
    M.exists_box_submersive_scheme T F hunimod eW hExp realize haarN b aN hm E γ hγ
      (scale ∘ u) (fun n => hscale (u n))
  refine ⟨u ∘ v, hu.comp hv, h, hh, target, z₀, ?_, htsub,
    m, letters, source, t₀, ?_, hssub⟩
  · exact ht.comp hv.tendsto_atTop
  · simpa only [Function.comp_def, rescaledLieData, boxBasis, boxCost] using hs

end PolycyclicRecognition.CartanWordModel

end

end OAI
