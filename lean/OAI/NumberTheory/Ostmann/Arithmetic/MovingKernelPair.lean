import OAI.NumberTheory.Ostmann.Arithmetic.MovingKernelRates

namespace OAI

/-! # The literal product of the two histories in a diagonal comparison -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

noncomputable def movingRealKernelPair {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) : ℂ :=
  movingRealKernel value (T false) (nodes false) ψ X lo hi hlo hhi φ G L R *
    conj (movingRealKernel value (T true) (nodes true) ψ X lo hi hlo hhi φ G L R)

theorem pairedPolynomialFactors_roots {n m : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor)
    (S U : Finset ℝ)
    (hS : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (hU : ∀ i r, r ∈ (G i).polynomial.derivative.roots → r ∈ U) :
    ∀ i r, r ∈ ((pairedPolynomialFactors F G) i).polynomial.derivative.roots → r ∈ S ∪ U := by
  intro i r
  refine Fin.addCases ?_ ?_ i
  · intro j hr
    simp only [pairedPolynomialFactors, Fin.append_left] at hr
    exact Finset.mem_union_left _ (hS j r hr)
  · intro j hr
    simp only [pairedPolynomialFactors, Fin.append_right, ClippedPolynomialFactor.conjugate] at hr
    exact Finset.mem_union_right _ (hU j r hr)

theorem movingPairedSmoothPolynomialFactors_budget {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    smoothPolynomialBudget (pairedPolynomialFactors
      (movingSmoothPolynomialFactors value (T false) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
      (movingSmoothPolynomialFactors value (T true) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)) ≤
      (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 := by
  rw [pairedPolynomialFactors_budget, pow_two]
  have h0 := movingSmoothPolynomialFactors_budget value (T false) L R ψ X lo hi V hlo hhi
    (hV false) φ G B D hB hD hφ hlip
  have h1 := movingSmoothPolynomialFactors_budget value (T true) L R ψ X lo hi V hlo hhi
    (hV true) φ G B D hB hD hφ hlip
  exact mul_le_mul h0 h1 (smoothPolynomialBudget_nonneg _) ((smoothPolynomialBudget_nonneg _).trans h0)

theorem movingRealKernelPair_norm {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B) (L R : ℝ) :
    ‖movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G L R‖ ≤
      ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2 := by
  rw [movingRealKernelPair, norm_mul, Complex.norm_conj, pow_two]
  exact mul_le_mul
    (movingRealKernel_norm value (T false) (nodes false) ψ X lo hi hlo hhi φ G B hB hφ L R)
    (movingRealKernel_norm value (T true) (nodes true) ψ X lo hi hlo hhi φ G B hB hφ L R)
    (norm_nonneg _) (by positivity)

theorem measurable_movingRealKernelPair {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0) :
    Measurable (fun z : ℝ × ℝ => movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G z.1 z.2) := by
  have h0 := measurable_movingRealKernel value (T false) (nodes false) ψ X lo hi hlo hhi φ G
    B D hB hD hφ hlip hout
  have h1 := measurable_movingRealKernel value (T true) (nodes true) ψ X lo hi hlo hhi φ G
    B D hB hD hφ hlip hout
  exact h0.mul (Complex.continuous_conj.measurable.comp h1)

theorem movingRealKernelPair_slice_polynomial {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (coord : Bool) (fixed z : ℝ) :
    let W := fun b => movingSmoothPolynomialFactors value (T b)
      (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
    movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G
      (movingRealPair coord fixed z false) (movingRealPair coord fixed z true) =
      (movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed z) *
        conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed z))) *
        smoothPolynomialWeight (pairedPolynomialFactors (W false) (W true)) z := by
  dsimp only
  rw [movingRealKernelPair,
    movingRealKernel_slice_polynomial value (T false) (nodes false) ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip hout,
    movingRealKernel_slice_polynomial value (T true) (nodes true) ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip hout,
    pairedPolynomialFactors_weight, map_mul]
  ring

theorem movingRealKernelPair_slice_root_data {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (coord : Bool) (fixed : ℝ) :
    let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
    let W := fun b => movingSmoothPolynomialFactors value (T b)
      (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
    ∃ S : Finset ℝ, S.card + 1 ≤ 2 * movingKernelRootBudget n ∧
      (∀ i r, r ∈ ((pairedPolynomialFactors (W false) (W true)) i).polynomial.derivative.roots → r ∈ S) ∧
      (∀ x y, rootCellCode S x = rootCellCode S y →
        (movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed x) *
          conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed x))) =
        (movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed y) *
          conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed y)))) := by
  dsimp only
  obtain ⟨S, hS, hSr, hSc⟩ := movingRealKernel_slice_root_data value hvalue childBound pivotBound
    (T false) (hf false) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip coord fixed
  obtain ⟨U, hU, hUr, hUc⟩ := movingRealKernel_slice_root_data value hvalue childBound pivotBound
    (T true) (hf true) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip coord fixed
  refine ⟨S ∪ U, ?_, pairedPolynomialFactors_roots _ _ S U hSr hUr, ?_⟩
  · have hc := Finset.card_union_le S U
    unfold movingKernelRootBudget
    omega
  · intro x y hc
    rw [hSc x y (rootCellCode_eq_of_subset S (S ∪ U) Finset.subset_union_left x y hc),
      hUc x y (rootCellCode_eq_of_subset U (S ∪ U) Finset.subset_union_right x y hc)]

end Ostmann

end OAI
