import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTerminalComparison
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ChronologicalAlternatingHaar
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BundleParameterCharts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalExponentialMeasure

namespace OAI

/-! # Comparing an alternating target product with the terminal cover

The product-image theorem is applied to the correlated increment set itself.
Its terminal lifts then give a volume comparison in the original Lie group.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold Topology ENNReal

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
  [SecondCountableTopology F.N.carrier]

theorem alternating_product_exponent_le
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
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (β β₁ β₂ : M.Bases) (E E₁ E₂ : Set W)
    {h cN : ℕ} (hh : 0 < h) (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hn : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale RH R η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 < scale n) (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) (hη : Tendsto η atTop (𝓝 0))
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
    (I : ℕ → Set (Fin (h * 2) → F.N.carrier)) (hIc : ∀ n, IsCompact (I n))
    (hbox₁ : ∀ n u, u ∈ I n → ∀ j : Fin h,
      u (finProdFinEquiv (j, (0 : Fin 2))) ∈
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E₁ β₁ (scale n) (R n))
    (hbox₂ : ∀ n u, u ∈ I n → ∀ j : Fin h,
      u (finProdFinEquiv (j, (1 : Fin 2))) ∈
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E₂ β₂ (scale n) (R n))
    (hvol : HasSubexponentialLowerBoundSeq scale (fun n =>
      ((Measure.pi fun _ : Fin (h * 2) =>
        Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume) (I n)).toReal /
      Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
        (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val))))
    (s : ℕ → Finset (Fin (h * 2) → G))
    (p : ℕ → (Fin (h * 2) → G) → (Fin (h * 2) → F.N.carrier) × (Fin (h * 2) → F.D.carrier))
    (U : Set ((Fin (h * 2) → F.N.carrier) × (Fin (h * 2) → F.D.carrier))) (hU : IsCompact U)
    (t : ℕ → Finset G) {ρ Rc q : ℝ}
    (hp : ∀ n x, x ∈ s n → ∀ i,
      F.inclusionN ((p n x).1 i) * F.inclusionD ((p n x).2 i) = x i)
    (hsmall : ∀ z ∈ U, dist (1 : Fin (h * 2) → G)
      (fun i => F.inclusionN (z.1 i) * F.inclusionD (z.2 i)) < ρ)
    (hd : ∀ n x, x ∈ s n → ∀ i,
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i))‖ ≤ RH n)
    (hhgt : ∀ n x, x ∈ s n → ∀ i,
      ‖eW (heightProjection T.character
        (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i) : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤
          η n * scale n)
    (hI : ∀ n u, u ∈ I n → ∃ x ∈ s n, ∃ z ∈ U,
      prefixCoordinateEquiv (h * 2) u = fun i => (p n x).1 i * F.action ((p n x).2 i) (z.1 i))
    (hcover : ∀ᶠ n in atTop, ∀ x ∈ s n, ∃ y ∈ t n,
      dist (x ⟨h * 2 - 1, Nat.sub_lt (by omega) (by decide)⟩) y ≤ Rc)
    (hcount : HasSubexponentialUpperBoundSeq scale
      (fun n => ((t n).card : ℝ) / Real.exp (scale n * q))) :
    columnBasisWeight (M.boxCost T hunimod eW E) β.val ≤ q := by
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  obtain ⟨C, _, hCI, hClower⟩ := chronological_alternating_haar_image F.N.equiv F.ExpN
    chartN hchartN F.isExpN.map_zero aN hm M.letter M.wordList b₀ β β₁ β₂
    (M.boxCost T hunimod eW E) (M.boxCost T hunimod eW E₁) (M.boxCost T hunimod eW E₂)
    (bundleOutputChart (h + h) _) scale hs rem hn p₀ hlim z₀ hsub R hR0 hR I hIc hbox₁ hbox₂ hvol
  exact M.terminal_product_exponent_le T F hunimod eW hExpG hinjG realize π hπ hπExp
    chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN μ b₀ β (by omega)
    scale RH η hs hscale hRH0 hRH hη s p U hU I C t hp hsmall hd hhgt hI hCI hClower hcover hcount

end PolycyclicRecognition.CartanWordModel

end

end OAI
