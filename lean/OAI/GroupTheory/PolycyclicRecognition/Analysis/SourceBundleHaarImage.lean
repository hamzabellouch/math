import OAI.GroupTheory.PolycyclicRecognition.Algebra.BundleWordImage
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledTupleVolume
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledAlternatingEndpoints
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearHaarCoordinates

namespace OAI

/-! # Joint source-bundle Haar volume before conjugation

The polynomial image is taken in the product of all bundle coordinates.
Thus a correlated restriction of the common parameter set is retained.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set
open scoped Manifold Topology

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype I]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

def sourceBundleProduct {m h M : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (X : I → L) (s : I → ℝ)
    (letters : Fin m → I)
    (input : (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ)) (r : ℝ)
    (t : Fin M → ℝ) : Fin h → G := fun j =>
  (List.ofFn (fun k : Fin m => Exp (lie
    (((input t j) (Fin.castAdd m k) - (input t j) (Fin.natAdd m k)) •
      (Real.exp (r * s (letters k)) • X (letters k)))))).prod

theorem source_bundle_haar_image_sequence {m h c M N : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ) (s : I → ℝ) (letters : Fin m → I)
    (input : (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ))
    (output : (Fin N → ℝ) ≃L[ℝ] (Fin h → Fin (finrank ℝ L) → ℝ))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hN : 1 ≤ N)
    (p₀ : WordLawData I (finrank ℝ L))
    (hlim : Tendsto (fun r =>
      let b := exponentialRescaleBasis (WordBasisSelections.basis X words β)
        (fun j => cost (β.val j)) (scale r)
      (basisBracket b, fun i => b.equivFun (Real.exp (scale r * s i) • X i))) atTop (𝓝 p₀))
    (t₀ : Fin (m + m) → ℝ)
    (hs : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters p₀) t₀))
    (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r) (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (hanchor : ∀ r, ‖input.symm (fun _ => t₀)‖ ≤ R r)
    (A : ℕ → Set (Fin M → ℝ)) (hA : ∀ r, MeasurableSet (A r))
    (hAR : ∀ r, A r ⊆ Metric.closedBall 0 (R r))
    (hAlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (A r)).toReal)) :
    ∃ C : ℕ → Set (Fin h → G), (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ sourceBundleProduct lie Exp X s letters input (scale r) '' A r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r =>
        ((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume)) (C r)).toReal /
          Real.exp (scale r * ((h : ℝ) * columnBasisWeight cost β.val))) := by
  let b := fun r => exponentialRescaleBasis (WordBasisSelections.basis X words β)
    (fun j => cost (β.val j)) (scale r)
  let p : ℕ → WordLawData I (finrank ℝ L) := fun r =>
    (basisBracket (b r), fun i => (b r).equivFun (Real.exp (scale r * s i) • X i))
  obtain ⟨K, hK, hKA, hKlower⟩ := bundle_word_image_sequence scale hscale rem hN a letters
    input output p p₀ hlim t₀ hs R hR hRupper hanchor A hA hAR hAlower
  let T := fun r => exponentialTupleCoordinates lie chart (fun _ : Fin h => b r)
  let C := fun r => (T r).symm '' (output '' K r)
  have hC (r : ℕ) : IsCompact (C r) :=
    ((hK r).image output.continuous).image (T r).symm.continuous
  refine ⟨C, hC, ?_, ?_⟩
  · filter_upwards [hKA] with r hr
    rintro y ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨t, ht, htw⟩ := hr hw
    refine ⟨t, ht, ?_⟩
    rw [← htw]
    funext j
    change _ = exponentialBasisHomeomorph lie chart (b r)
      (output (bundleWordEndpoint a letters input output (p r) t) j)
    rw [bundleWordEndpoint, ContinuousLinearEquiv.apply_symm_apply,
      exponentialBasisHomeomorph_apply lie Exp chart hchart]
    exact (exp_rescaled_differenceWord (b r) (Exp ∘ lie) (by simpa using hzero) a
      (model_binary_dynkin lie Exp a hm) X s (scale r) letters (input t j)).symm
  · have hvol := rescaled_tuple_image_volume_lower_sequence scale hscale lie Exp chart hchart
      X words b₀ (fun _ : Fin h => β) (fun _ => cost) (fun r => output '' K r)
      (hKlower.linear_image hscale output)
    change HasSubexponentialLowerBoundSeq scale (fun r =>
      ((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume)) (C r)).toReal /
        Real.exp (scale r * ∑ _i : Fin h, columnBasisWeight cost β.val)) at hvol
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hvol

end PolycyclicRecognition

end

end OAI
