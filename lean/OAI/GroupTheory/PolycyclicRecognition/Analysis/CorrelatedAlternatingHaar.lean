import OAI.GroupTheory.PolycyclicRecognition.Analysis.AlternatingHaarImage
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlternatingTupleCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedTupleDomain

namespace OAI

/-! # Alternating products of correlated lifted tuples

No independence is required of the retained tuple set. The product rank
is a property of the full limiting multiplication map.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Manifold Topology

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

theorem correlated_alternating_haar_image {m h c : ℕ}
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
    (S : ℕ → Set (Fin (h + h) → G)) (hS : ∀ r, IsCompact (S r))
    (hbox : ∀ r u, u ∈ S r → ∀ i, u i ∈ exponentialCoordinateBox (Exp ∘ lie)
      (rescaledTupleBases X words (Fin.addCases (fun _ => β₁) (fun _ => β₂))
        (Fin.addCases (fun _ => cost₁) (fun _ => cost₂)) (scale r) i) (R r))
    (hlower : HasSubexponentialLowerBoundSeq scale (fun r =>
      ((Measure.pi (fun _ : Fin (h + h) =>
        Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume)) (S r)).toReal /
      Real.exp (scale r * ∑ i : Fin (h + h), columnBasisWeight
        (Fin.addCases (fun _ => cost₁) (fun _ => cost₂) i)
        ((Fin.addCases (motive := fun _ : Fin (h + h) => WordBasisSelections X words)
          (fun _ => β₁) (fun _ => β₂) i).val)))) :
    ∃ C : ℕ → Set G, (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun u : Fin (h + h) → G =>
        (List.ofFn (fun j : Fin h => u (Fin.castAdd h j) * u (Fin.natAdd h j))).prod) '' S r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r =>
        ((Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume) (C r)).toReal /
          Real.exp (scale r * columnBasisWeight cost β.val)) := by
  let pairβ : Fin (h + h) → WordBasisSelections X words :=
    Fin.addCases (fun _ => β₁) (fun _ => β₂)
  let pairCost : Fin (h + h) → words → ℝ :=
    Fin.addCases (fun _ => cost₁) (fun _ => cost₂)
  let bs := fun r => rescaledTupleBases X words pairβ pairCost (scale r)
  let f := fun r => flatExponentialTupleCoordinates lie chart (bs r) flat
  let A := fun r => f r '' S r
  obtain ⟨hAc, hAR, hRflat, hAlower⟩ := normalized_tuple_domain lie Exp chart hchart X words b₀
    pairβ pairCost
    flat scale hscale R hR hRupper S hS hbox hlower
  let b₁ := fun r => exponentialRescaleBasis (WordBasisSelections.basis X words β₁)
    (fun j => cost₁ (β₁.val j)) (scale r)
  let b₂ := fun r => exponentialRescaleBasis (WordBasisSelections.basis X words β₂)
    (fun j => cost₂ (β₂.val j)) (scale r)
  let pairFlat := flat.trans (alternatingTupleSplit h)
  obtain ⟨C, hC, hCA, hClower⟩ := alternating_haar_image_growing_sequence lie Exp chart hchart
    hzero a hm X words b₀ β cost b₁ b₂ pairFlat scale hscale rem hn p₀ hlim z₀ hs
    (fun r => ‖flat.symm.toContinuousLinearMap‖ * R r) (fun r => mul_nonneg (norm_nonneg _) (hR r))
    hRflat A (fun r => (hAc r).measurableSet) hAR hAlower
  refine ⟨C, hC, ?_, hClower⟩
  filter_upwards [hCA] with r hr
  rintro y hy
  obtain ⟨x, ⟨u, hu, hxu⟩, hxy⟩ := hr hy
  refine ⟨u, hu, ?_⟩
  rw [← hxu] at hxy
  rw [← hxy]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  have he₁ : (pairFlat (f r u) j).1 =
      (exponentialBasisHomeomorph lie chart (b₁ r)).symm (u (Fin.castAdd h j)) := by
    change ((flat.trans (alternatingTupleSplit h))
      (flat.symm (exponentialTupleCoordinates lie chart (bs r) u)) j).1 = _
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
      alternatingTupleSplit_apply]
    change (exponentialBasisHomeomorph lie chart (bs r (Fin.castAdd h j))).symm
      (u (Fin.castAdd h j)) = _
    simp only [bs, rescaledTupleBases, pairβ, pairCost, Fin.addCases_left, b₁]
  have he₂ : (pairFlat (f r u) j).2 =
      (exponentialBasisHomeomorph lie chart (b₂ r)).symm (u (Fin.natAdd h j)) := by
    change ((flat.trans (alternatingTupleSplit h))
      (flat.symm (exponentialTupleCoordinates lie chart (bs r) u)) j).2 = _
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
      alternatingTupleSplit_apply]
    change (exponentialBasisHomeomorph lie chart (bs r (Fin.natAdd h j))).symm
      (u (Fin.natAdd h j)) = _
    simp only [bs, rescaledTupleBases, pairβ, pairCost, Fin.addCases_right, b₂]
  rw [he₁, he₂, ← exponentialBasisHomeomorph_apply lie Exp chart hchart,
    ← exponentialBasisHomeomorph_apply lie Exp chart hchart,
    Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

end PolycyclicRecognition

end

end OAI
