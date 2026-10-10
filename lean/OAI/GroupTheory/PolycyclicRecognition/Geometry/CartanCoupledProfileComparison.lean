import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSourceTargetComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSourceBundleTerminals
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTargetBundlePaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCoupledTargetTuples

namespace OAI

/-! # The actual coupled source-to-target profile comparison

A positive common good set supplies all tuples and all their paths. No
independence of the bundles, terminal-cover bound, or volume estimate is a premise.
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

theorem exists_coupled_profile_comparison_region
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
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let br := fun n => exponentialRescaleBasis b
      (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (scale n))
    let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ Q : Set (Fin (finrank ℝ H) → ℝ), IsCompact Q ∧
      Q ⊆ {z | height (b.equivFun.symm z) ∈ V} ∧
      ∀ {Λ : ℝ≥0}, 0 < (Λ : ℝ) → ∀ (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
        (R : ℕ → ℝ) (k₀ : ℕ → F.N.carrier) (k : ℕ → Fin (h * 2) → F.N.carrier)
        (Good : ℕ → Set F.N.carrier) (ε δ : ℕ → ℝ),
        (∀ n, 0 ≤ R n) → HasSubexponentialUpperBoundSeq scale R →
        (∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) (R n)) →
        (∀ n i, k n i ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) (R n)) →
        (∀ n, MeasurableSet (Good n)) →
        (∀ n, Good n ⊆ (fun y => y * k₀ n) ''
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1) →
        (∀ n, 0 < ((Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume) (Good n)).toReal) →
        HasSubexponentialLowerBoundSeq scale (fun n =>
          ((Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume) (Good n)).toReal /
          ((Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume)
            ((fun y => y * k₀ n) '' M.groupBox T hunimod eW
              (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1)).toReal) →
        (∀ n, 0 ≤ ε n) → Tendsto ε atTop (𝓝 0) →
        (∀ n, 0 ≤ δ n) → Tendsto δ atTop (𝓝 0) →
        (∀ᶠ n in atTop, ∀ i,
          dist (ExpG (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
            (F.inclusionN (k n i) * ExpG (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤
              δ n * scale n) →
        (∀ᶠ n in atTop, ∀ i (q : F.N.carrier), q ∈ Good n → ∀ z ∈ Q, height (b.equivFun.symm z) ∈ E →
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
              (F.inclusionN (q * k n i)) (Real.log (scale n))
              (fun z => ExpG ((br n).equivFun.symm z)) z -
            (A i (height (b.equivFun.symm z)) + offset i)‖ ≤ ε n) →
        columnBasisWeight (M.boxCost T hunimod eW (E₁ ∪ E₂)) β.val ≤
          (M.supportIn T hunimod eW).templateSupport E := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  dsimp only
  have hscale0 n : 0 < scale n := lt_of_lt_of_le zero_lt_one (hscale1 n)
  obtain ⟨Q, hQ, hQV, hgeom⟩ := M.exists_target_bundle_geometry T F eW hExpG realize
    haarD dynkinD π hπExp X hDnil bD₀ βD hβD scale hscale hscale0
    pivot v E V hE hpivot hV hVconv hEV hv s hs (h := h * 2) letters ρ (by linarith)
  refine ⟨Q, hQ, hQV, ?_⟩
  intro Λ hΛ p x R k₀ k Good ε δ hR0 hR hk₀ hk hGood hGoodQ hGoodpos hGoodmass
    hε0 hε hδ0 hδ hbridge hgood
  let pivotD := fun n => F.ExpD (F.D.equiv (scale n • pivot))
  have hpivotD n : F.inclusionD (pivotD n) =
      ExpG (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := F.compatibleD _
  obtain ⟨initial, S, t, hi, hS, ht, hsep, hcount, hreach⟩ := M.exists_coupled_target_tuples
    T F hunimod eW hExpG realize haarN haarD dynkinN b₀ cell E βcell γ hβcell s hsCell
    letters aN hm scale R hscale (fun n => (hscale0 n).le) hR0 hR ρ hρ k₀ k hk₀ hk rem
    (Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega)))
    sourceLimit hsourceLimit t₀ hsourceSub Good hGood hΛ p x pivotD
    hGoodQ hGoodpos hGoodmass
  have hboundary : ∀ᶠ n in atTop, ∀ v ∈ S n,
      ∃ z : Fin ((h * 2) * m + (h * 2) * m) → ℝ, ‖z‖ ≤ ρ ∧
        SwitchSuccessful (fun _ => Good n) 0 ((h * 2) * m) (initial n)
          (sampledSwitchParameters
            (coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
              (fun j : Fin ((h * 2) * m) => letters (finProdFinEquiv.symm j).2)
              M.letter s (scale n) (bundleConjugator m (k n))) ((h * 2) * m) z) ∧
        ∀ i : Fin (h * 2), v i = sourceBundleBoundary (initial n)
          (fun i => MulAut.conj (k n i))
          (sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
            (bundleParameterChart (h * 2) m) (scale n) z) (i.val + 1) := by
    filter_upwards [hreach] with n hn
    intro v hv
    obtain ⟨_, z, hz, hs, he⟩ := hn v hv
    refine ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, hs, ?_⟩
    intro i
    rw [he]
    exact (sourceBundleBoundary_eq_stateEquiv (initial n) (fun i => MulAut.conj (k n i))
      (fun i => (innerContinuousMulEquiv (k n i)).toHomeomorph.toMeasurableEquiv)
      (fun _ _ => rfl) _ i).symm
  obtain ⟨D, η, hD, hη0, hη, htarget⟩ := hgeom p hLip Good x k A offset ε δ initial S
    hi hε0 hε hδ0 hδ hbridge hgood hboundary hpath
  obtain ⟨Cs, hCs, hsource⟩ := M.exists_source_bundle_terminal_bounds T F eW
    hExpG realize haarD dynkinD π hπExp X hDnil bD₀ βD hβD scale hscale hscale0
    pivot v E V hE hpivot hV hVconv hEV hv s hs letters ρ (by linarith)
    (by omega) hbijN hLip hpath Good x k initial hi S δ hδ0 hδ hbridge hboundary
  let pivotG := fun n => ExpG (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let origin := fun n => x n * F.inclusionN (initial n) * pivotG n
  let last : Fin (h * 2) := ⟨h * 2 - 1, by omega⟩
  let terminals := fun n => relativeTupleTerminals F.inclusionN (origin n) (x n) (pivotG n) last (S n)
  let E₀ := (fun w => w - eW (heightProjection T.character pivot)) '' E
  have hE₀ : IsCompact E₀ := hEc.image (continuous_id.sub continuous_const)
  have h0E₀ : (0 : W) ∈ E₀ := ⟨_, hpivot, sub_self _⟩
  have hnum : HasSubexponentialLowerBoundSeq scale (fun n => ((t n).card : ℝ) /
      Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
        (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val))) := by
    have he : ((h * 2 : ℕ) : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E) γ.val =
        (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
          (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val := by
      rw [M.columnBasisWeight_eq_templateSupport_of_maximizing T hunimod eW b₀ E γ hγ,
        M.columnBasisWeight_eq_templateSupport_of_maximizing T hunimod eW b₀ E₁ β₁ hβ₁,
        M.columnBasisWeight_eq_templateSupport_of_maximizing T hunimod eW b₀ E₂ β₂ hβ₂,
        hP₁, hP₂]
      push_cast
      ring
    simpa only [he] using hcount
  have hle := M.source_target_product_exponent_le T F hunimod eW hExpG hinjG realize rem
    π hLip.continuous hπExp chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD
    haarN haarD b₀ β β₁ β₂ (E₁ ∪ E₂) E₁ E₂ hh aN hm hdim scale η hscale hscale1 hη0 hη
    hpath hLip D D hD hD targetLimit htargetLimit z₀ htargetSub hE₁ hE₂ h01 h02 hβ₁ hβ₂ ν
    t ?_ hsep hnum E₀ hE₀ ⟨0, h0E₀⟩ terminals
    (fun n => (isCompact_relativeTupleTerminals F.inclusionN F.closedN.continuous
      (origin n) (x n) (pivotG n) last (hS n)).totallyBounded) hCs hsource
    (fun n => normalizedTranslate (origin n) (p n)) (fun _ => 1) ?_
  · have he : (M.supportIn T hunimod eW).templateSupport E₀ =
        (M.supportIn T hunimod eW).templateSupport E := by
      simpa only [E₀, sub_eq_add_neg] using
        (M.supportIn T hunimod eW).templateSupport_translate hEc ⟨_, hpivot⟩
          (-eW (heightProjection T.character pivot))
    exact he ▸ hle
  · filter_upwards [htarget] with n hn
    intro y hy
    have hymem := ht n hy
    simp only [hpivotD] at hymem
    obtain ⟨paths, hm, hh, he⟩ := hn y hymem
    refine ⟨paths, hm, ?_, he⟩
    intro i u
    obtain ⟨w, hw, he⟩ := hh i u
    exact ⟨w, (himage i).subset hw, he⟩
  · filter_upwards [] with n
    intro y hy
    have hymem := ht n hy
    simp only [hpivotD] at hymem
    obtain ⟨z, hz, he⟩ := centered_image_terminal_mem (p n) F.inclusionN
      (origin n) (x n) (pivotG n) last (S n) hymem
    exact ⟨z, hz, by simpa only [one_mul] using he⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
