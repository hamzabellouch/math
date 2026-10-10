import OAI.GroupTheory.PolycyclicRecognition.Analysis.SourceBundleHaarImage
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BundleParameterCharts
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSuccessfulParameterMass
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceSampledSuccessfulVolume

namespace OAI

/-! # Backward recurrence produces the actual joint source-bundle volume

All bundle schemes and their number are fixed before the successful
parameter set is selected. The image is taken before conjugating bundles.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set Metric
open scoped Manifold Topology ENNReal NNReal

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype I]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

theorem recurrent_source_bundle_haar_image_sequence {m h c : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ) (s : I → ℝ) (letters : Fin m → I)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hN : 1 ≤ h * finrank ℝ L)
    (p₀ : WordLawData I (finrank ℝ L))
    (hlim : Tendsto (fun r =>
      let b := exponentialRescaleBasis (WordBasisSelections.basis X words β)
        (fun j => cost (β.val j)) (scale r)
      (basisBracket b, fun i => b.equivFun (Real.exp (scale r * s i) • X i))) atTop (𝓝 p₀))
    (t₀ : Fin (m + m) → ℝ)
    (hs : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters p₀) t₀))
    (ρ : ℝ) (hρ : 1 ≤ ρ)
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (sample : ℕ → ℕ → ℝ → G) (σ : ℕ → ℕ → Measure G)
    [∀ r j, IsProbabilityMeasure (σ r j)]
    (hsample : ∀ r j, MeasurePreserving (sample r j) (uniformIntervalLaw ρ) (σ r j))
    (Q Good : ℕ → Set G) (K V : ℕ → ℕ → Set G) (D : ℕ → ℕ → ℝ)
    (hQfin : ∀ r, μ (Q r) ≠ ∞) (hQpos : ∀ r, 0 < (μ (Q r)).toReal)
    (hK : ∀ r j, ∀ᵐ v ∂σ r j, v ∈ K r j)
    (hVfin : ∀ r j, μ (V r j) ≠ ∞) (hVpos : ∀ r j, 0 < (μ (V r j)).toReal)
    (hQV : ∀ r j, ∀ x ∈ Q r, ∀ v ∈ K r j, x * v ∈ V r j)
    (hD : ∀ r j, 0 < D r j)
    (hdenom : ∀ r j, (μ (V r j)).toReal ≤ D r j * (μ (Q r)).toReal)
    (hGood : ∀ r, MeasurableSet (Good r)) (hGoodQ : ∀ r, Good r ⊆ Q r)
    (hGoodpos : ∀ r, 0 < (μ (Good r)).toReal)
    (hGoodlower : HasSubexponentialLowerBoundSeq scale
      (fun r => (μ (Good r)).toReal / (μ (Q r)).toReal))
    (hDupper : ∀ j, j < h * m → HasSubexponentialUpperBoundSeq scale (fun r => D r j)) :
    ∃ (x : ℕ → G) (C : ℕ → Set (Fin h → G)),
      (∀ r, x r ∈ Good r) ∧ (∀ r, IsCompact (C r)) ∧
      HasSubexponentialLowerBoundSeq scale (fun r =>
        ((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume)) (C r)).toReal /
          Real.exp (scale r * ((h : ℝ) * columnBasisWeight cost β.val))) ∧
      ∀ᶠ r in atTop, ∀ y ∈ C r, ∃ t : Fin (h * m + h * m) → ℝ,
        t ∈ closedBall 0 ρ ∧
        SwitchSuccessful (fun _ => Good r) 0 (h * m) (x r)
          (sampledSwitchParameters (sample r) (h * m) t) ∧
        sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) (scale r) t = y := by
  obtain ⟨x, B, hx, hB, hprob, hsuccess⟩ := exists_subexponential_successful_parameters_sequence
    scale hscale μ σ Q Good K V D hQfin hQpos hK hVfin hVpos hQV hD hdenom (h * m)
    hGood hGoodQ hGoodpos hGoodlower hDupper
  obtain ⟨A, hA, hAρ, hAlower, hAsuccess⟩ := exists_sampled_success_volume_sequence
    (zero_lt_one.trans_le hρ) (h * m) scale hscale sample σ hsample x Good B hB hprob hsuccess
  let R := 1 + ρ + ‖(bundleParameterChart h m).symm (fun _ => t₀)‖
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg ((bundleParameterChart h m).symm (fun _ => t₀))]
  have hρR : ρ ≤ R := by dsimp [R]; linarith [norm_nonneg ((bundleParameterChart h m).symm (fun _ => t₀))]
  have hanchor : ‖(bundleParameterChart h m).symm (fun _ => t₀)‖ ≤ R := by dsimp [R]; linarith
  obtain ⟨C, hC, hCA, hClower⟩ := source_bundle_haar_image_sequence lie Exp chart hchart
    hzero a hm X words b₀ β cost s letters (bundleParameterChart h m) (bundleOutputChart h _)
    scale hscale rem hN p₀ hlim t₀ hs (fun _ => R) (fun _ => hR)
    (sequence_subexponential_upper_const hscale R) (fun _ => hanchor) A hA
    (fun r => (hAρ r).trans (closedBall_subset_closedBall hρR)) hAlower
  refine ⟨x, C, hx, hC, hClower, ?_⟩
  filter_upwards [hCA] with r hr
  intro y hy
  obtain ⟨t, ht, hty⟩ := hr hy
  exact ⟨t, hAρ r ht, hAsuccess r t ht, hty⟩

end PolycyclicRecognition

end

end OAI
