import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCoupledRecurrenceCells
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoupledRootIntervals
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RecurrentSourceBundles
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalExponentialMeasure

namespace OAI

/-! # Joint source-bundle images for the actual coupled recurrence

The interval laws and all recurrence denominators are constructed here.
Only the good-profile mass and the full normalized source-map submersion
remain to be supplied by the profile selection.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set Metric
open scoped Manifold Topology ENNReal

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
  [MeasurableSpace N] [BorelSpace N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (haar : NilpotentExponentialHaarInput EN N) (dynkin : NilpotentDynkinExpansionInput EN N)

include hExp haar dynkin in
theorem coupled_source_bundle_haar_image_sequence
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E source : Set W) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, s i ≤ (M.supportIn T hunimod eW).weightSupport E i)
    {m h c : ℕ} (letters : Fin m → Fin M.letterCount)
    (aN : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial aN ![x, y]) = Exp x * Exp y)
    (scale R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (k₀ : ℕ → N) (k : ℕ → ℕ → N)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n))
    (hk : ∀ n j, k n j ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n))
    (rem : RemezPolynomialInput) (hN : 1 ≤ h * finrank ℝ (cartanRootIdeal H))
    (p₀ : WordLawData (Fin M.letterCount) (finrank ℝ (cartanRootIdeal H)))
    (hlim : Tendsto (fun r =>
      let b := M.boxBasis T hunimod eW source γ (scale r)
      (basisBracket b, fun i => b.equivFun (Real.exp (scale r * s i) • M.letter i))) atTop (𝓝 p₀))
    (t₀ : Fin (m + m) → ℝ)
    (hsub : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters p₀) t₀))
    (Good : ℕ → Set N) (hGood : ∀ n, MeasurableSet (Good n)) :
    let μ := Measure.map ((Exp ∘ eN) ∘ b₀.equivFun.symm) volume
    let Q := fun n => (fun y => y * k₀ n) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) 1
    let allLetters := fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2
    let sample := fun n => coupledRootIntervalSample (Exp ∘ eN) allLetters M.letter s (scale n) (k n)
    (∀ n, Good n ⊆ Q n) → (∀ n, 0 < (μ (Good n)).toReal) →
    HasSubexponentialLowerBoundSeq scale (fun n => (μ (Good n)).toReal / (μ (Q n)).toReal) →
    ∃ (x : ℕ → N) (C : ℕ → Set (Fin h → N)),
      (∀ n, x n ∈ Good n) ∧ (∀ n, IsCompact (C n)) ∧
      HasSubexponentialLowerBoundSeq scale (fun n =>
        ((Measure.pi fun _ : Fin h => μ) (C n)).toReal /
          Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW source) γ.val))) ∧
      ∀ᶠ n in atTop, ∀ y ∈ C n, ∃ t : Fin (h * m + h * m) → ℝ,
        t ∈ closedBall 0 ρ ∧
        SwitchSuccessful (fun _ => Good n) 0 (h * m) (x n)
          (sampledSwitchParameters (sample n) (h * m) t) ∧
        sourceBundleProduct eN Exp M.letter s letters (bundleParameterChart h m) (scale n) t = y := by
  dsimp only
  intro hGoodQ hGoodpos hGoodlower
  let : IsTopologicalGroup N := topologicalGroup_of_lieGroup (𝓘(ℝ, EN)) ⊤
  have hnil : LieRing.IsNilpotent (cartanRootIdeal H) :=
    (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
  obtain ⟨⟨chart, hchart⟩, _⟩ := haar.2 Exp hExp (eN.nilpotent_iff_equiv_nilpotent.mp hnil)
  let coords := exponentialBasisHomeomorph eN chart b₀
  let : LocallyCompactSpace N := coords.symm.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology N := coords.symm.secondCountableTopology
  let μ := Measure.map ((Exp ∘ eN) ∘ b₀.equivFun.symm) volume
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haar eN hnil Exp hExp b₀
  let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haar eN hnil Exp hExp b₀
  have hc (v : cartanRootIdeal H) : Continuous (fun t : ℝ => (Exp ∘ eN) (t • v)) := by
    have he (t : ℝ) : (Exp ∘ eN) (t • v) = chart (t • eN v) := by
      simp only [Function.comp_apply, map_smul, hchart]
    simp_rw [he]
    exact chart.continuous.comp (continuous_id.smul continuous_const)
  let allLetters := fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2
  let sample := fun n => coupledRootIntervalSample (Exp ∘ eN) allLetters M.letter s (scale n) (k n)
  let σ := fun n => coupledRootIntervalLaw (Exp ∘ eN) allLetters M.letter s (scale n) ρ (k n)
  let K := fun n j => (fun u => k n j * u * (k n j)⁻¹) ''
    rootIntervalSupport (Exp ∘ eN) allLetters M.letter s (scale n) ρ j
  let Q := fun n => (fun y => y * k₀ n) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) 1
  let : ∀ n j, IsProbabilityMeasure (σ n j) := fun n j =>
    coupledRootIntervalLaw_isProbability (Exp ∘ eN) allLetters M.letter s (scale n)
      (zero_lt_one.trans_le hρ) (k n) j
  obtain ⟨V, D, _, hDupper, hDpos, hcells, hcontain⟩ := M.exists_coupled_interval_recurrence_cells
    T hunimod eW eN Exp hExp haar dynkin b₀ E β hβ s hs allLetters scale R hscale hscale0
    hR0 hR ρ (zero_le_one.trans hρ) k₀ k hk₀ hk
  let Q' := fun n => (fun y => y * k₀ n) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (V n)
  exact recurrent_source_bundle_haar_image_sequence eN Exp chart hchart hExp.map_zero aN hm
    M.letter M.wordList b₀ γ (M.boxCost T hunimod eW source) s letters scale hscale rem hN p₀ hlim
    t₀ hsub ρ hρ μ sample σ
    (fun n j => measurePreserving_coupledRootIntervalSample (Exp ∘ eN) hc allLetters M.letter s (scale n) ρ (k n) j)
    Q Good K (fun n _ => Q' n) (fun n _ => D n)
    (fun n => (hcells n).1) (fun n => (hcells n).2.1)
    (fun n j => coupledRootIntervalLaw_ae_mem_support (Exp ∘ eN) hc allLetters M.letter s (scale n) ρ (k n) j)
    (fun n _ => (hcells n).2.2.1) (fun n _ => (hcells n).2.2.2.1)
    (fun n j x hx u hu => by
      obtain ⟨v, hv, rfl⟩ := hu
      exact hcontain n j x hx v hv)
    (fun n _ => hDpos n) (fun n _ => (hcells n).2.2.2.2.le)
    hGood hGoodQ hGoodpos hGoodlower (fun _ _ => hDupper)

end PolycyclicRecognition.CartanWordModel

end

end OAI
