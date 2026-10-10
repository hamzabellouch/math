import OAI.NumberTheory.Ostmann.Arithmetic.MovingRealKernel
import OAI.NumberTheory.Ostmann.Arithmetic.RootIntegralRates

namespace OAI

/-! # Concrete polynomial data for either slice of the two-giant kernel -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingSmoothPolynomialFactors_root_data {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ)
    (hL : L.natDegree ≤ 1) (hR : R.natDegree ≤ 1) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    ∃ S : Finset ℝ, S.card ≤ 2 ^ n ∧ ∀ i r,
      r ∈ ((movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
        φ G B D hB hD hφ hlip i).polynomial.derivative).roots → r ∈ S := by
  let F := movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi
  let S := polynomialRootCuts (fun i => (F i).polynomial.derivative)
  have hdeg (i : Fin (2 ^ n)) : (F i).polynomial.derivative.natDegree ≤ 1 := by
    have h := movingFourierPolynomialFactors_degree value T L R ψ X lo hi hlo hhi hL hR i
    change (F i).polynomial.natDegree ≤ 2 at h
    exact (Polynomial.natDegree_derivative_le _).trans (by omega)
  refine ⟨S, ?_, ?_⟩
  · exact (polynomialRootCuts_card _).trans (by
      calc
        _ ≤ ∑ _i : Fin (2 ^ n), 1 := Finset.sum_le_sum (fun i _ => hdeg i)
        _ = _ := by simp)
  · intro i r
    refine Fin.addCases ?_ ?_ i
    · intro j hr
      simp only [movingSmoothPolynomialFactors, Fin.append_left] at hr
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Multiset.mem_toFinset.mpr hr⟩
    · intro j
      simp only [movingSmoothPolynomialFactors, Fin.append_right]
      rw [movingNodeCutoffFactors_no_derivative_roots value T L R hL hR φ G B D hB hD hφ hlip j]
      simp

theorem movingRealKernel_slice_polynomial {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (coord : Bool) (fixed z : ℝ) :
    movingRealKernel value T nodes ψ X lo hi hlo hhi φ G
      (movingRealPair coord fixed z false) (movingRealPair coord fixed z true) =
      movingRealGateWeight value T nodes X lo hi (movingRealPair coord fixed z) *
        smoothPolynomialWeight (movingSmoothPolynomialFactors value T
          (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
          ψ X lo hi hlo hhi φ G B D hB hD hφ hlip) z := by
  rw [movingSmoothPolynomialFactors_real value T _ _ ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout,
    (movingCoordinate_eval coord fixed z).1, (movingCoordinate_eval coord fixed z).2]
  unfold movingRealKernel
  congr 2
  funext b
  cases coord <;> cases b <;> rfl

/-- The root count is uniform in both real coordinate values and all fixed
small primes. This is the certificate used by the joint giant comparison. -/
theorem movingRealKernel_slice_root_data {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (coord : Bool) (fixed : ℝ) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    let W := movingSmoothPolynomialFactors value T
      (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
    ∃ S : Finset ℝ,
      S.card ≤ (2 ^ n - 1) * (3 * (7 * 2 ^ n)) + 5 * 2 ^ n ∧
      (∀ i r, r ∈ (W i).polynomial.derivative.roots → r ∈ S) ∧
      (∀ x y, rootCellCode S x = rootCellCode S y →
        movingRealGateWeight value T nodes X lo hi (movingRealPair coord fixed x) =
        movingRealGateWeight value T nodes X lo hi (movingRealPair coord fixed y)) := by
  dsimp only
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
  obtain ⟨S, hS, hroot⟩ := movingSmoothPolynomialFactors_root_data value T
    (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
    (by cases coord <;> simp [movingCoordinateLeft])
    (by cases coord <;> simp [movingCoordinateRight]) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
  refine ⟨movingRealRootCuts value T nodes X lo hi coord fixed ∪ S, ?_, ?_, ?_⟩
  · have ha := movingRealRootCuts_card value hvalue childBound pivotBound T hf X lo hi coord fixed
    exact (Finset.card_union_le _ _).trans (by dsimp only [nodes]; omega)
  · intro i r hr
    exact Finset.mem_union_right _ (hroot i r hr)
  · intro x y hcode
    exact movingRealGateWeight_rootCell value T nodes X lo hi coord fixed x y _
      Finset.subset_union_left hcode

end Ostmann

end OAI
