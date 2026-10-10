import OAI.Combinatorics.Progressions.Lattices.AveragedAffineGrid

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem exists_averaged_affine_l1_from_input_bounds
    {W D G Z α : Type*} [MeasurableSpace W]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
    (he : ∀ d, Function.Injective (Sum.elim (eK d) (eN d)))
    (index : ∀ d, B d → J d ⊕ N d)
    (hindex : ∀ d b, Sum.elim (eK d) (eN d) (index d b) = canonicalPrincipalExponent h d b)
    (c w : ∀ d, J d ⊕ N d → ℝ) (hw : ∀ d j, 0 < w d j)
    (R : D → ℝ≥0) (hsupport : ∀ d j, |c d j|+w d j ≤ R d)
    (z : W → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (hclow : ∀ d o, c₀ d ≤ |c d (index d (block d o))|-|w d (index d (block d o))|)
    (hcup : ∀ d o, |c d (index d (block d o))|+|w d (index d (block d o))| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A L : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith L Real.smoothTransition)
    (extra : G → Option α → Z) {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d j, (Sum.elim (eK d) (eN d) j).sum (fun _ n => n) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hcsum : ∀ d, (∑ b, (|c d (index d b)|+|w d (index d b)|)) ≤ Csum)
    (hwsum : ∀ d, (∑ j, affineCoefficientAllowance (c d j) (w d j)) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) {P E : ℝ} (hP : 0 ≤ P)
    (hE : 0 ≤ E)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hAP : (A : ℝ) ≤ Real.exp P) (hLP : (L : ℝ) ≤ Real.exp P)
    (hCsumP : Csum ≤ Real.exp P) (hWsumP : Wsum ≤ Real.exp P)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    let P' := affineComparisonInputLog (B := B) (O := O) (α := α)
      (AffineAuxiliaryIndex Z (fun d => J d ⊕ N d)) h degree P E
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ)⁻¹ ≤ Real.exp (2*P'+2) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t⁻¹ ≤ Real.exp (6*P'+8) ∧
      ∀ (M : ∀ d, Matrix (O d) (J d) ℤ) (s : ∀ d, O d ↪ J d)
        (hM : ∀ d, ((M d).submatrix id (s d)).det ≠ 0)
        (S : ∀ d, J d → ℝ) (hS : ∀ d j, 0 < S d j)
        (Q : D → ℝ) (hQ : ∀ d, 0 < Q d)
        (T : SamplerTupleIndex G B h → ℝ), (∀ k, 0 < T k) →
      (∀ a x d, normalizedIntegerColumns (M d) (S d) (fun _ => Q d) =
        realJetMatrix (fun j => MvPolynomial.monomial (eK d j) 1)
          (normalizedCubeTuple (canonicalTupleInput extra) (z a) x) (sets d)) →
      ∀ μ : Measure W, IsProbabilityMeasure μ → (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      let E := fun d => normalizedPivotEquiv ((M d).submatrix id (s d)) (hM d)
        (fun j => S d (s d j)) (fun _ => Q d) (fun j => hS d (s d j)) (fun _ => hQ d)
      let F := fun d => matrixSupCLM
        (normalizedIntegerColumns (remainingMatrixColumns (M d) (s d)) (fun j => S d j.val) (fun _ => Q d))
      (∫ p : W × ((Σ d, O d) → ℝ),
        |averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets δ p.2 -
          smallAffineMixtureDensity h eK eN s E F sets extra c w t z p.1 p.2| ∂μ.prod volume) ≤ ε := by
  obtain ⟨hNoise, hm, hK, hM, hQbudget, hAccuracy⟩ :=
    affineComparisonInputLog_bounds (B := B) (O := O) (α := α)
      (AffineAuxiliaryIndex Z (fun d => J d ⊕ N d)) h hh c₀ C hc₀ hC A L degree
      hCsum hWsum hε hP hE hcP hCP hAP hLP hCsumP hWsumP hεE
  exact exists_averaged_affine_l1_with_parameter_bounds
    h hh eK eN he index hindex c w hw R hsupport z hz sets hsets hcard block hblock
    c₀ C hc₀ hC hclow hcup ψ hψ hrange hzero hone A L hLip hTransition extra
    hdegree htaildegree hCsum hWsum hcsum hwsum hε
    (affineComparisonInputLog_nonneg (B := B) (O := O) (α := α)
      (AffineAuxiliaryIndex Z (fun d => J d ⊕ N d)) h degree hP hE)
    hNoise hm hK hM hQbudget hAccuracy

end Erdos3

end

end OAI
