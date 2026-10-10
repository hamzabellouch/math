import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterKernel

namespace OAI

/-! # Root and variation bounds with the original outer giant priors -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem smoothPolynomialBudget_append {n m : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (G : Fin m → ClippedPolynomialFactor) :
    smoothPolynomialBudget (Fin.append F G) = smoothPolynomialBudget F * smoothPolynomialBudget G := by
  unfold smoothPolynomialBudget
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

noncomputable def movingOuterPolynomialFactors {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (diagonal : Bool) :=
  Fin.append (pairedPolynomialFactors
    (movingSmoothPolynomialFactors value (T false) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
    (movingSmoothPolynomialFactors value (T true) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip))
    (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal)

theorem movingOuterPolynomialFactors_budget {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (diagonal : Bool) :
    smoothPolynomialBudget (movingOuterPolynomialFactors value T L R ψ X lo hi hlo hhi φ G
      Jleft Jright B D hB hD hφ hlip diagonal) ≤
      (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 *
        ((2 * B + D * (Real.exp 2 - 1)) ^ 2 * (if diagonal then 1 + Real.exp 2 else 2)) := by
  have houter : 0 ≤ (2 * B + D * (Real.exp 2 - 1)) ^ 2 *
      (if diagonal then 1 + Real.exp 2 else 2) := by split <;> positivity
  rw [movingOuterPolynomialFactors, smoothPolynomialBudget_append, giantOuterFactors_budget]
  exact mul_le_mul_of_nonneg_right
    (movingPairedSmoothPolynomialFactors_budget value T L R ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip) houter

theorem giantOuterFactors_slice_no_roots (φ : ℝ → ℝ) (Jleft Jright B D : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (diagonal coord : Bool) (fixed : ℝ) (i : Fin 3) :
    ((giantOuterFactors (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      φ Jleft Jright B D hB hD hφ hlip diagonal i).polynomial.derivative).roots = 0 := by
  fin_cases i <;> cases coord <;> cases diagonal <;>
    simp [giantOuterFactors, movingCoordinateLeft, movingCoordinateRight,
      giantReciprocalFactor, reciprocalPolynomialFactor, logCutoffPolynomialFactor,
      Polynomial.derivative_mul, Polynomial.roots_C]

theorem movingOuterKernel_slice_roots {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (diagonal coord : Bool) (fixed : ℝ) :
    let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
    let W := movingOuterPolynomialFactors value T (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal
    ∃ S : Finset ℝ, S.card + 1 ≤ 2 * movingKernelRootBudget n ∧
      (∀ i r, r ∈ (W i).polynomial.derivative.roots → r ∈ S) ∧
      (∀ x y, rootCellCode S x = rootCellCode S y →
        (movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed x) *
          conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed x))) =
        (movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed y) *
          conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed y)))) := by
  dsimp only
  obtain ⟨S, hS, hroots, hconst⟩ := movingRealKernelPair_slice_root_data value hvalue childBound pivotBound
    T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip coord fixed
  refine ⟨S, hS, ?_, hconst⟩
  intro i r
  refine Fin.addCases ?_ ?_ i
  · intro j hj
    apply hroots j r
    simpa only [movingOuterPolynomialFactors, Fin.append_left] using hj
  · intro j hj
    simp only [movingOuterPolynomialFactors, Fin.append_right,
      giantOuterFactors_slice_no_roots φ Jleft Jright B D hB hD hφ hlip diagonal coord fixed j,
      Multiset.notMem_zero] at hj

end Ostmann

end OAI
