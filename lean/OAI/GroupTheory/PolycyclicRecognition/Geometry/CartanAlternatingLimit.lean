import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanAlternatingSchemes

namespace OAI

/-! # The actual convergent alternating data used by the terminal comparison -/

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

theorem exists_alternating_box_limit
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (b : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {c : ℕ} (aN : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (E₁ E₂ : Set W) (hE₁ : IsCompact E₁) (hne₁ : E₁.Nonempty)
    (hE₂ : IsCompact E₂) (hne₂ : E₂.Nonempty)
    (β β₁ β₂ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW (E₁ ∪ E₂)) β.val)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW E₂) β₂.val)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 ≤ scale n)
    (hn : 1 ≤ finrank ℝ (cartanRootIdeal H)) :
    ∃ u : ℕ → ℕ, StrictMono u ∧ ∃ h : ℕ, 0 < h ∧
      ∃ (p₀ : AlternatingLawData (finrank ℝ (cartanRootIdeal H)))
        (z₀ : Fin h → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ×
          (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)),
        Tendsto (fun n =>
          let bU := M.boxBasis T hunimod eW (E₁ ∪ E₂) β (scale (u n))
          let b₁ := M.boxBasis T hunimod eW E₁ β₁ (scale (u n))
          let b₂ := M.boxBasis T hunimod eW E₂ β₂ (scale (u n))
          (basisBracket bU, boxCoordinateChange bU b₁, boxCoordinateChange bU b₂))
          atTop (𝓝 p₀) ∧
        Function.Surjective (fderiv ℝ
          (alternatingCoordinateProduct aN p₀.1 p₀.2.1 p₀.2.2) z₀) := by
  obtain ⟨C, _, q₀, _, _, u, hu, hlim, h, z₀, _, hsub⟩ :=
    M.exists_alternating_box_scheme T F hunimod eW hExp realize haarN b aN hm
      E₁ E₂ hE₁ hne₁ hE₂ hne₂ β β₁ β₂ hβ hβ₁ hβ₂ scale hscale
  let p₀ : AlternatingLawData (finrank ℝ (cartanRootIdeal H)) := (q₀.1.1.1, q₀.1.2)
  have hh : 0 < h := alternating_submersion_length_pos hn aN p₀ z₀ hsub
  refine ⟨u, hu, h, hh, p₀, z₀, ?_, hsub⟩
  have hprojection : Continuous (fun q : TwoImageData (Fin M.letterCount)
      (finrank ℝ (cartanRootIdeal H)) => (q.1.1.1, q.1.2)) :=
    continuous_fst.fst.fst.prodMk continuous_fst.snd
  have hlim' := hprojection.continuousAt.tendsto.comp hlim
  have hmax : (M.supportIn T hunimod eW).weightSupport (E₁ ∪ E₂) =
      fun i => max ((M.supportIn T hunimod eW).weightSupport E₁ i)
        ((M.supportIn T hunimod eW).weightSupport E₂ i) := by
    funext i
    exact (M.supportIn T hunimod eW).weightSupport_union hE₁ hne₁ hE₂ hne₂ i
  simpa only [Function.comp_def, rescaledTwoImageData, rescaledLieData,
    boxBasis, boxCost, hmax, p₀] using hlim'

end PolycyclicRecognition.CartanWordModel

end

end OAI
