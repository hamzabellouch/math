import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCoupledProfileComparison
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceCellProfilePairs
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCellProbability

namespace OAI

/-! # A supported pair supplies the coupled profile comparison

The common good set, positive mass, and error rate are all selected from the
actual joint weak law. The scale and both polynomial limits stay fixed.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]


variable [Fintype I] [DecidableEq I]

theorem coupled_comparison_of_supported_cell_profiles
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) {Kπ : ℝ≥0}
    (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
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
    (E V cell E₁ E₂ : Set W) (hEc : IsCompact E) (hE : Convex ℝ E)
    (pivot : H) (hpivot : eW (heightProjection T.character pivot) ∈ E)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : E ⊆ V)
    (v : Fin M.letterCount → H)
    (hv : ∀ i, eW (heightProjection T.character (pivot + v i : H)) ∈ E)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (pivot + v i : H)))) = s i)
    (hsCell : ∀ i, s i ≤ (M.supportIn T hunimod eW).weightSupport cell i)
    (β β₁ β₂ βcell γ : M.Bases)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₂) β₂.val)
    (hβcell : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) γ.val)
    (hE₁ : IsCompact E₁) (hE₂ : IsCompact E₂) (h01 : (0 : W) ∈ E₁) (h02 : (0 : W) ∈ E₂)
    (hP₁ : (M.supportIn T hunimod eW).templateSupport E₁ =
      (M.supportIn T hunimod eW).templateSupport E)
    (hP₂ : (M.supportIn T hunimod eW).templateSupport E₂ =
      (M.supportIn T hunimod eW).templateSupport E)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {m h cN : ℕ} (letters : Fin m → Fin M.letterCount) (hh : 0 < h)
    (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    (sourceLimit : WordLawData (Fin M.letterCount) (finrank ℝ (cartanRootIdeal H)))
    (hsourceLimit : Tendsto (fun n =>
      let b := M.boxBasis T hunimod eW E γ (scale n)
      (basisBracket b, fun i => b.equivFun (Real.exp (scale n * s i) • M.letter i)))
      atTop (𝓝 sourceLimit))
    (t₀ : Fin (m + m) → ℝ)
    (hsourceSub : Function.Surjective
      (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters sourceLimit) t₀))
    (targetLimit : AlternatingLawData (finrank ℝ (cartanRootIdeal H)))
    (htargetLimit : Tendsto (fun n =>
      let b := M.boxBasis T hunimod eW (E₁ ∪ E₂) β (scale n)
      let b₁ := M.boxBasis T hunimod eW E₁ β₁ (scale n)
      let b₂ := M.boxBasis T hunimod eW E₂ β₂ (scale n)
      (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂))
      atTop (𝓝 targetLimit))
    (z₀ : Fin h → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ×
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (htargetSub : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct aN targetLimit.1 targetLimit.2.1 targetLimit.2.2) z₀))
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure] [SigmaFinite ν]
    (ρ : ℝ) (hρ : 1 ≤ ρ)
    (A : Fin (h * 2) → W →ₗ[ℝ] W) (offset : Fin (h * 2) → W)
    (himage : ∀ i, (fun w => A i (w - eW (heightProjection T.character pivot))) '' E =
      alternatingCoordinateFamily h E₁ E₂ i)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (R : ℕ → ℝ) (k₀ : ℕ → F.N.carrier) (k : ℕ → Fin (h * 2) → F.N.carrier)
    (δ : ℕ → ℝ)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) (R n))
    (hk : ∀ n i, k n i ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) (R n))
    (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (hbridge : ∀ᶠ n in atTop, ∀ i,
      dist (ExpG (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (F.inclusionN (k n i) * ExpG (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤
          δ n * scale n)
    (SP : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace SP] [BorelSpace SP] [BorelSpace (SP × SP)] [HasOuterApproxClosed (SP × SP)]
    (profile : ℕ → F.N.carrier → SP × SP) (hprofile : ∀ n, Measurable (profile n))
    (limit : ProbabilityMeasure (SP × SP)) (f : SP × SP)
    (hf : f ∈ (limit : Measure (SP × SP)).support) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let br := fun n => exponentialRescaleBasis b
      (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (scale n))
    let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    let Qcell := fun n => (fun y => y * k₀ n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1
    Tendsto (fun n => ProbabilityMeasure.map
        (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ cell βcell
          (scale n) (k₀ n)) (profile n))
        atTop (𝓝 limit) →
      (∀ n i q, q ∈ Qcell n → ∀ z,
        alternatingCoordinateFamily h (profile n q).1.val (profile n q).2.val i z =
          rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN (q * k n i)) (Real.log (scale n))
            (fun z => ExpG ((br n).equivFun.symm z)) z) →
      (∀ i z, height (b.equivFun.symm z) ∈ E →
        alternatingCoordinateFamily h f.1.val f.2.val i z =
          A i (height (b.equivFun.symm z)) + offset i) →
      columnBasisWeight (M.boxCost T hunimod eW (E₁ ∪ E₂)) β.val ≤
        (M.supportIn T hunimod eW).templateSupport E := by
  dsimp only
  intro hlimit hactual haffine
  let hcell := fun n => M.translated_groupBox_cell_properties T F hunimod eW
    haarN chartN hchartN b₀ cell βcell (scale n) (k₀ n)
  obtain ⟨Q, hQ, _, hcompare⟩ := M.exists_coupled_profile_comparison_region
    T F hunimod eW hExpG hinjG realize rem π hLip hπExp chartN hchartN chartD hchartD
    hbijN hbijD dynkinN dynkinD haarN haarD b₀ E V cell E₁ E₂ hEc hE pivot hpivot
    hV hVconv hEV v hv s hs hsCell β β₁ β₂ βcell γ hβ₁ hβ₂ hβcell hγ hE₁ hE₂ h01 h02
    hP₁ hP₂ X hDnil bD₀ βD hβD letters hh aN hm hdim scale hscale hscale1
    sourceLimit hsourceLimit t₀ hsourceSub targetLimit htargetLimit z₀ htargetSub ν ρ hρ
    A offset himage hpath
  obtain ⟨Good, err, hGood, hGoodQ, herr0, herr, hGoodpos, hGoodmass, happ⟩ :=
    exists_positive_eventually_good_cell_profile_pairs SP Q hQ scale hscale
      (Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume)
      (fun n => (fun y => y * k₀ n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1)
      (fun n => (hcell n).1) (fun n => (hcell n).2.1) (fun n => (hcell n).2.2)
      profile hprofile limit hlimit hf
  apply hcompare hΛ p x R k₀ k Good err δ hR0 hR hk₀ hk hGood hGoodQ hGoodpos hGoodmass
    (fun n => (herr0 n).le) herr hδ0 hδ hbridge
  filter_upwards [happ] with n hn
  intro i q hq z hz hzE
  have hboth := hn q hq z hz
  have he : ‖alternatingCoordinateFamily h (profile n q).1.val (profile n q).2.val i z -
      alternatingCoordinateFamily h f.1.val f.2.val i z‖ < err n := by
    unfold alternatingCoordinateFamily
    split_ifs
    · exact hboth.1
    · exact hboth.2
  rw [hactual n i q (hGoodQ n hq) z, haffine i z hzE] at he
  exact he.le

end PolycyclicRecognition.CartanWordModel

end

end OAI
