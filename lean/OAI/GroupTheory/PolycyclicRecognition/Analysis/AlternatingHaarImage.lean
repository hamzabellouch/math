import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledAlternatingEndpoints
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledTupleVolume

namespace OAI

/-! # Haar-volume rate of the actual alternating product

The compact coordinate image furnished by scalar Remez is transported
through the actual exponential chart. The output determinant is the
weight of the union template, not the sum of the input weights.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set
open scoped Manifold Topology

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

theorem alternating_haar_image_growing_sequence {m h c : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ)
    (b₁ b₂ : ℕ → Basis (Fin (finrank ℝ L)) ℝ L)
    (e : (Fin m → ℝ) ≃L[ℝ]
      (Fin h → (Fin (finrank ℝ L) → ℝ) × (Fin (finrank ℝ L) → ℝ)))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ finrank ℝ L)
    (p₀ : AlternatingLawData (finrank ℝ L))
    (hlim : Tendsto (fun r =>
      let b := exponentialRescaleBasis (WordBasisSelections.basis X words β)
        (fun j => cost (β.val j)) (scale r)
      (basisBracket b, boxCoordinateChange b (b₁ r), boxCoordinateChange b (b₂ r)))
      atTop (𝓝 p₀))
    (z₀ : Fin h → (Fin (finrank ℝ L) → ℝ) × (Fin (finrank ℝ L) → ℝ))
    (hs : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct a p₀.1 p₀.2.1 p₀.2.2) z₀))
    (R : ℕ → ℝ) (hR : ∀ r, 0 ≤ R r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (A : ℕ → Set (Fin m → ℝ)) (hA : ∀ r, MeasurableSet (A r))
    (hAR : ∀ r, A r ⊆ Metric.closedBall 0 (R r))
    (hAlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (A r)).toReal)) :
    ∃ C : ℕ → Set G,
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => (List.ofFn (fun j =>
        Exp (lie ((b₁ r).equivFun.symm (e x j).1)) *
        Exp (lie ((b₂ r).equivFun.symm (e x j).2)))).prod) '' A r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r =>
        ((Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume) (C r)).toReal /
          Real.exp (scale r * columnBasisWeight cost β.val)) := by
  let b := fun r => exponentialRescaleBasis (WordBasisSelections.basis X words β)
    (fun j => cost (β.val j)) (scale r)
  let p : ℕ → AlternatingLawData (finrank ℝ L) := fun r =>
    (basisBracket (b r), boxCoordinateChange (b r) (b₁ r), boxCoordinateChange (b r) (b₂ r))
  obtain ⟨K, hK, hKA, hKlower⟩ := alternating_product_image_growing_sequence a e
    scale hscale rem hn p p₀ hlim z₀ hs R hR hRupper A hA hAR hAlower
  let f := fun r => (Exp ∘ lie) ∘ (b r).equivFun.symm
  have hf (r : ℕ) : f r = exponentialBasisHomeomorph lie chart (b r) := by
    funext x
    exact (exponentialBasisHomeomorph_apply lie Exp chart hchart (b r) x).symm
  refine ⟨fun r => f r '' K r, fun r => (hK r).image (by rw [hf]; fun_prop), ?_, ?_⟩
  · filter_upwards [hKA] with r hr
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hr hz
    refine ⟨x, hx, ?_⟩
    rw [← hxy]
    exact (exp_flatAlternatingProduct (b r) (b₁ r) (b₂ r) (Exp ∘ lie)
      (by simpa using hzero) a (model_binary_dynkin lie Exp a hm) e x).symm
  · let d := |(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det|
    have hd : 0 < d := abs_pos.mpr (wordBasis_det_ne_zero X words b₀ β)
    have he (r : ℕ) :
        ((Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume) (f r '' K r)).toReal /
          Real.exp (scale r * columnBasisWeight cost β.val) = d * (volume (K r)).toReal := by
      rw [exponential_rescaled_subset_measure lie Exp chart hchart X words b₀ β cost
        (scale r) (K r)]
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le,
        ENNReal.toReal_ofReal (Real.exp_pos _).le]
      field_simp
    simpa only [he] using (sequence_subexponential_lower_const hscale hd).mul hKlower

end PolycyclicRecognition

end

end OAI
