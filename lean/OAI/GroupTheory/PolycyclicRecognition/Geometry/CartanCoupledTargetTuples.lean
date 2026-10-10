import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCoupledSourceImage
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoupledBundleStates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSourceTuplePacking
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairAction

namespace OAI

/-! # Separated target tuples from the actual coupled source recurrence

Successful parameters survive the passage from the joint source image to
good source states and then to separated target tuples.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set Metric
open scoped Manifold Topology NNReal ENNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]

theorem exists_coupled_target_tuples
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E source : Set W) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, s i ≤ (M.supportIn T hunimod eW).weightSupport E i)
    {m h c : ℕ} (letters : Fin m → Fin M.letterCount)
    (aN : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (scale R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (k₀ : ℕ → F.N.carrier) (k : ℕ → Fin h → F.N.carrier)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n))
    (hk : ∀ n i, k n i ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n))
    (rem : RemezPolynomialInput) (hN : 1 ≤ h * finrank ℝ (cartanRootIdeal H))
    (p₀ : WordLawData (Fin M.letterCount) (finrank ℝ (cartanRootIdeal H)))
    (hlim : Tendsto (fun r =>
      let b := M.boxBasis T hunimod eW source γ (scale r)
      (basisBracket b, fun i => b.equivFun (Real.exp (scale r * s i) • M.letter i))) atTop (𝓝 p₀))
    (t₀ : Fin (m + m) → ℝ)
    (hsub : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters p₀) t₀))
    (Good : ℕ → Set F.N.carrier) (hGood : ∀ n, MeasurableSet (Good n))
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
    (base : ℕ → G) (pivot : ℕ → F.D.carrier) :
    let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
    let Q := fun n => (fun y => y * k₀ n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1
    let allLetters := fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2
    let sample := fun n => coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
      allLetters M.letter s (scale n) (bundleConjugator m (k n))
    (∀ n, Good n ⊆ Q n) → (∀ n, 0 < (μ (Good n)).toReal) →
    HasSubexponentialLowerBoundSeq scale (fun n => (μ (Good n)).toReal / (μ (Q n)).toReal) →
    ∃ (initial : ℕ → F.N.carrier) (S : ℕ → Set (Fin h → F.N.carrier))
      (t : ℕ → Finset (Fin h → G)),
      (∀ n, initial n ∈ Good n) ∧ (∀ n, IsCompact (S n)) ∧
      (∀ n, (↑(t n) : Set (Fin h → G)) ⊆ (fun v => fun i =>
        basedImage (p n).val.1 (base n * F.inclusionN (initial n) * F.inclusionD (pivot n))
          (base n * F.inclusionN (v i) * F.inclusionD (pivot n))) '' S n) ∧
      (∀ n u, u ∈ t n → ∀ v, v ∈ t n → u ≠ v → 1 ≤ dist u v) ∧
      HasSubexponentialLowerBoundSeq scale (fun n => ((t n).card : ℝ) /
        Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW source) γ.val))) ∧
      ∀ᶠ n in atTop, ∀ v ∈ S n, (∀ i, v i ∈ Good n) ∧
        ∃ z : Fin (h * m + h * m) → ℝ, z ∈ closedBall 0 ρ ∧
          SwitchSuccessful (fun _ => Good n) 0 (h * m) (initial n)
            (sampledSwitchParameters (sample n) (h * m) z) ∧
          v = sourceBundleStateEquiv h (initial n)
            (fun i => (innerContinuousMulEquiv (k n i)).toHomeomorph.toMeasurableEquiv)
            (sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
              (bundleParameterChart h m) (scale n) z) := by
  dsimp only
  intro hGoodQ hGoodpos hGoodlower
  let : LocallyCompactSpace F.N.carrier := F.closedN.locallyCompactSpace
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  have h1 n : (1 : F.N.carrier) ∈
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n) := by
    refine ⟨0, ?_, ?_⟩
    · simp only [Function.comp_apply, map_zero, F.isExpN.map_zero]
    · simpa only [map_zero, norm_zero] using hR0 n
  obtain ⟨initial, C, hi, hC, hvol, hreach⟩ := M.coupled_source_bundle_haar_image_sequence
    T hunimod eW F.N.equiv F.ExpN F.isExpN haarN dynkinN b₀ E source β γ hβ s hs letters aN hm
    scale R hscale hscale0 hR0 hR ρ hρ k₀ (fun n => bundleConjugator m (k n)) hk₀
    (fun n j => bundleConjugator_mem (k n) (h1 n) (hk n) j)
    rem hN p₀ hlim t₀ hsub Good hGood hGoodQ hGoodpos hGoodlower
  let S := fun n => sourceBundleStateEquiv h (initial n)
    (fun i => (innerContinuousMulEquiv (k n i)).toHomeomorph.toMeasurableEquiv) '' C n
  obtain ⟨hS, hSvol, hSreach⟩ := good_coupled_source_bundle_image F.N.equiv F.ExpN F.isExpN
    M.letter s letters scale _ μ k Good initial hi C hC hvol ρ hreach
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let origin := fun n => base n * F.inclusionN (initial n) * F.inclusionD (pivot n)
  let p' := fun n => normalizedTranslate (origin n) (p n)
  obtain ⟨t, ht, htsep, htcount⟩ := F.exists_target_source_tuple_count T M hExpG realize
    haarN haarD dynkinN hunimod μ hΛ p' hscale (fun n => (origin n)⁻¹ * base n) pivot S hS hSvol
  refine ⟨initial, S, t, hi, hS, ?_, htsep, htcount, hSreach⟩
  intro n y hy
  obtain ⟨v, hv, rfl⟩ := ht n hy
  refine ⟨v, hv, ?_⟩
  funext i
  simp only [p', normalizedTranslate, translatePair, ContinuousMap.coe_mk, basedImage]
  simp only [mul_assoc, mul_inv_cancel_left, origin]

end PolycyclicRecognition.CartanWordModel

end

end OAI
