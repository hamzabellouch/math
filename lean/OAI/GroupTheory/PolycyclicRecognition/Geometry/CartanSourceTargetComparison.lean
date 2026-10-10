import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPathAlternatingComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSourceTerminalCover
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateThickeningLimit

namespace OAI

/-! # Comparing target multiplication with actual source terminal paths -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]

theorem source_target_product_exponent_le
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) (hπ : Continuous (fun g => (π g).toAdd))
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (β β₁ β₂ : M.Bases) (E E₁ E₂ : Set W)
    {h cN : ℕ} (hh : 0 < h) (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hn : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n) (hη : Tendsto η atTop (𝓝 0))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ≥0} (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p₀ : AlternatingLawData (finrank ℝ (cartanRootIdeal H)))
    (hlim : Tendsto (fun n =>
      let b := M.boxBasis T hunimod eW E β (scale n)
      let b₁ := M.boxBasis T hunimod eW E₁ β₁ (scale n)
      let b₂ := M.boxBasis T hunimod eW E₂ β₂ (scale n)
      (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂)) atTop (𝓝 p₀))
    (z₀ : Fin h → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ×
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hsub : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct aN p₀.1 p₀.2.1 p₀.2.2) z₀))
    (hE₁ : IsCompact E₁) (hE₂ : IsCompact E₂) (h01 : (0 : W) ∈ E₁) (h02 : (0 : W) ∈ E₂)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₂) β₂.val)
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure] [SigmaFinite ν]
    (s : ℕ → Finset (Fin (h * 2) → G))
    (htarget : ∀ᶠ n in atTop, ∀ x, x ∈ s n →
      ∃ path : ∀ i : Fin (h * 2), Path (1 : G)
          ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1)),
        (∀ i, PathMetricBound (path i) (A * scale n)
          (B * (1 + Real.log (2 + scale n)))) ∧
        (∀ i u, ∃ z ∈ alternatingCoordinateFamily h E₁ E₂ i,
          ‖(π (path i u)).toAdd - scale n • z‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) ∧
        ∀ i : Fin (h * 2),
          ‖(π ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1))).toAdd‖ ≤
            η n * scale n)
    (hsep : ∀ n x, x ∈ s n → ∀ y, y ∈ s n → x ≠ y → 1 ≤ dist x y)
    (hnum : HasSubexponentialLowerBoundSeq scale (fun n => ((s n).card : ℝ) /
      Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
        (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val))))
    (Esrc : Set W) (hEsrc : IsCompact Esrc) (hne : Esrc.Nonempty)
    (S : ℕ → Set G) (hS : ∀ n, TotallyBounded (S n))
    {Cs bs : ℝ} (hCs : 0 ≤ Cs)
    (hsource : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z ∈ S n,
      ∃ path : Path (1 : G) z,
        PathMetricBound path (Cs * scale n) (Cs * (1 + Real.log (2 + scale n))) ∧
        ∀ t, ∃ w ∈ Esrc, ‖(π (path t)).toAdd - scale n • w‖ ≤
          ε * scale n + bs * (1 + Real.log (2 + scale n)))
    {Λ : ℝ≥0} (p : ℕ → NormalizedPair G Λ) (base : ℕ → G)
    (hterminal : ∀ᶠ n in atTop, ∀ x ∈ s n, ∃ z ∈ S n,
      x ⟨h * 2 - 1, Nat.sub_lt (by omega) (by decide)⟩ = (p n).val.1 (base n * z)) :
    columnBasisWeight (M.boxCost T hunimod eW E) β.val ≤
      (M.supportIn T hunimod eW).templateSupport Esrc := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp htarget
  let s' : ℕ → Finset (Fin (h * 2) → G) := fun n => if N ≤ n then s n else ∅
  have hsub' (n : ℕ) : s' n ⊆ s n := by
    dsimp only [s']
    split_ifs <;> simp
  have hpaths' n x (hx : x ∈ s' n) := by
    have hn : N ≤ n := by
      by_contra hn
      simp only [s', ite_eq_right hn, Finset.notMem_empty] at hx
    exact hN n hn x (hsub' n hx)
  have hnum' : HasSubexponentialLowerBoundSeq scale (fun n => ((s' n).card : ℝ) /
      Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
        (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val))) := by
    intro ε hε
    filter_upwards [hnum ε hε, eventually_ge_atTop N] with n hn hlarge
    simpa only [s', ite_eq_left hlarge] using hn
  obtain ⟨t, hcover, hcount⟩ := M.exists_normalized_source_terminal_cover T F hunimod eW π
    hπExp chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD hExpG realize b₀ β
    hpath hLip hEsrc hne scale hs S hS hCs hsource p base
  apply (M.supportIn T hunimod eW).le_templateSupport_of_thickenings hEsrc hne
  intro ε hε
  apply M.path_alternating_product_exponent_le (Rc := (Λ : ℝ)) T F hunimod eW hExpG hinjG realize rem
    π hπ hπExp chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN haarD
    b₀ β β₁ β₂ E E₁ E₂ hh aN hm hn scale η hs hscale hη0 hη hpath Kπ.coe_nonneg
    (fun x y => by simpa only [dist_eq_norm] using hLip.dist_le_mul x y)
    A B hA hB p₀ hlim z₀ hsub hE₁ hE₂ h01 h02 hβ₁ hβ₂ ν s' t hpaths' (fun n x hx y hy => hsep n x (hsub' n hx) y (hsub' n hy)) hnum' ?_
    (hcount ε hε)
  filter_upwards [hterminal] with n hn
  intro x hx
  obtain ⟨z, hz, he⟩ := hn x (hsub' n hx)
  obtain ⟨y, hy, hd⟩ := hcover n z hz
  refine ⟨y, hy, ?_⟩
  rw [he]
  exact hd

end PolycyclicRecognition.CartanWordModel

end

end OAI
