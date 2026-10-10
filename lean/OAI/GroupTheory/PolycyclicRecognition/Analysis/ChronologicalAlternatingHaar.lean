import OAI.GroupTheory.PolycyclicRecognition.Analysis.CorrelatedAlternatingHaar
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlternatingWordOrder

namespace OAI

/-! # The union-template Haar rate for actual chronological increments -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set
open scoped Manifold Topology

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype I]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

omit [Fintype I] in
theorem chronological_alternating_haar_image {m h c : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β β₁ β₂ : WordBasisSelections X words) (cost cost₁ cost₂ : words → ℝ)
    (flat : (Fin m → ℝ) ≃L[ℝ] (Fin (h + h) → Fin (finrank ℝ L) → ℝ))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ finrank ℝ L)
    (p₀ : AlternatingLawData (finrank ℝ L))
    (hlim : Tendsto (fun r =>
      let b := exponentialRescaleBasis (WordBasisSelections.basis X words β)
        (fun j => cost (β.val j)) (scale r)
      let b₁ := exponentialRescaleBasis (WordBasisSelections.basis X words β₁)
        (fun j => cost₁ (β₁.val j)) (scale r)
      let b₂ := exponentialRescaleBasis (WordBasisSelections.basis X words β₂)
        (fun j => cost₂ (β₂.val j)) (scale r)
      (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂)) atTop (𝓝 p₀))
    (z₀ : Fin h → (Fin (finrank ℝ L) → ℝ) × (Fin (finrank ℝ L) → ℝ))
    (hs : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct a p₀.1 p₀.2.1 p₀.2.2) z₀))
    (R : ℕ → ℝ) (hR : ∀ r, 0 ≤ R r) (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (S : ℕ → Set (Fin (h * 2) → G)) (hS : ∀ r, IsCompact (S r))
    (hbox₁ : ∀ r u, u ∈ S r → ∀ j : Fin h,
      u (finProdFinEquiv (j, (0 : Fin 2))) ∈ exponentialCoordinateBox (Exp ∘ lie)
        (exponentialRescaleBasis (WordBasisSelections.basis X words β₁)
          (fun i => cost₁ (β₁.val i)) (scale r)) (R r))
    (hbox₂ : ∀ r u, u ∈ S r → ∀ j : Fin h,
      u (finProdFinEquiv (j, (1 : Fin 2))) ∈ exponentialCoordinateBox (Exp ∘ lie)
        (exponentialRescaleBasis (WordBasisSelections.basis X words β₂)
          (fun i => cost₂ (β₂.val i)) (scale r)) (R r))
    (hlower : HasSubexponentialLowerBoundSeq scale (fun r =>
      ((Measure.pi (fun _ : Fin (h * 2) =>
        Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume)) (S r)).toReal /
      Real.exp (scale r * ((h : ℝ) * columnBasisWeight cost₁ β₁.val +
        (h : ℝ) * columnBasisWeight cost₂ β₂.val)))) :
    ∃ C : ℕ → Set G, (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun u : Fin (h * 2) → G => (List.ofFn u).prod) '' S r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r =>
        ((Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume) (C r)).toReal /
          Real.exp (scale r * columnBasisWeight cost β.val)) := by
  let μ := Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume
  have he : ((Exp ∘ lie) ∘ b₀.equivFun.symm) = exponentialBasisHomeomorph lie chart b₀ := by
    funext x
    exact (exponentialBasisHomeomorph_apply lie Exp chart hchart b₀ x).symm
  let : SigmaFinite μ := by
    dsimp only [μ]
    rw [he]
    exact (exponentialBasisHomeomorph lie chart b₀).measurableEmbedding.sigmaFinite_map
  let B := fun r => alternatingWordBlockEquiv h '' S r
  have hB : ∀ r, IsCompact (B r) := fun r =>
    (hS r).image (continuous_alternatingWordBlockEquiv h)
  have hbox : ∀ r u, u ∈ B r → ∀ i, u i ∈ exponentialCoordinateBox (Exp ∘ lie)
      (rescaledTupleBases X words (Fin.addCases (fun _ => β₁) (fun _ => β₂))
        (Fin.addCases (fun _ => cost₁) (fun _ => cost₂)) (scale r) i) (R r) := by
    rintro r u ⟨v, hv, rfl⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [alternatingWordBlockEquiv_left, rescaledTupleBases, Fin.addCases_left] using hbox₁ r v hv j
    · simpa only [alternatingWordBlockEquiv_right, rescaledTupleBases, Fin.addCases_right] using hbox₂ r v hv j
  have hmass (r : ℕ) : (Measure.pi fun _ : Fin (h + h) => μ) (B r) =
      (Measure.pi fun _ : Fin (h * 2) => μ) (S r) :=
    alternatingWordBlockEquiv_image_measure h μ (S r)
  dsimp only [μ] at hmass
  have hweight : (∑ i : Fin (h + h), columnBasisWeight
      (Fin.addCases (fun _ => cost₁) (fun _ => cost₂) i)
      ((Fin.addCases (motive := fun _ : Fin (h + h) => WordBasisSelections X words)
        (fun _ => β₁) (fun _ => β₂) i).val)) =
      (h : ℝ) * columnBasisWeight cost₁ β₁.val + (h : ℝ) * columnBasisWeight cost₂ β₂.val := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  obtain ⟨C, hC, hCB, hClower⟩ := correlated_alternating_haar_image lie Exp chart hchart
    hzero a hm X words b₀ β β₁ β₂ cost cost₁ cost₂ flat scale hscale rem hn p₀ hlim z₀ hs
    R hR hRupper B hB hbox (by simpa only [hmass, hweight] using hlower)
  refine ⟨C, hC, ?_, hClower⟩
  filter_upwards [hCB] with r hr
  rintro y hy
  obtain ⟨u, ⟨v, hv, rfl⟩, he⟩ := hr hy
  exact ⟨v, hv, (alternatingWordBlockEquiv_prod h v).symm.trans he⟩

end PolycyclicRecognition

end

end OAI
