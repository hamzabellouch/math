import OAI.NumberTheory.Ostmann.Arithmetic.MovingNodeCutoffFactor
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFourierBudget

namespace OAI

/-! # One polynomial family for all node cutoffs and Fourier leaves -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingSmoothPolynomialFactors {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    Fin (2 ^ n + (T.nodeCutoffPolynomials value L R).length) → ClippedPolynomialFactor :=
  Fin.append (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi)
    (movingNodeCutoffFactors value T L R φ G B D hB hD hφ hlip)

theorem movingSmoothPolynomialFactors_value {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (z : ℝ) :
    smoothPolynomialWeight (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip) z =
      smoothPolynomialWeight (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) z *
        movingRealNodeCutoff value φ G T (L.eval z) (R.eval z) := by
  simp only [smoothPolynomialWeight, movingSmoothPolynomialFactors, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right]
  exact congrArg (_ * ·) (movingNodeCutoffFactors_value value T L R φ G B D hB hD hφ hlip hout z)

theorem movingSmoothPolynomialFactors_budget {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V)) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    smoothPolynomialBudget (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip) ≤
      movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1) := by
  have he : smoothPolynomialBudget (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
        φ G B D hB hD hφ hlip) =
      smoothPolynomialBudget (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) *
        smoothPolynomialBudget (movingNodeCutoffFactors value T L R φ G B D hB hD hφ hlip) := by
    simp only [smoothPolynomialBudget, movingSmoothPolynomialFactors, Fin.prod_univ_add,
      Fin.append_left, Fin.append_right]
  rw [he, movingNodeCutoffFactors_budget]
  apply mul_le_mul_of_nonneg_right
    (movingFourierPolynomialFactors_budget value T L R ψ X lo hi V hlo hhi hV)
  have he2 : 0 ≤ Real.exp (2 : ℝ) - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  positivity

/-- The complete smooth family uses only the Fourier leaves' derivative
roots. Logarithmic node cutoffs add no cuts and no large-center factor. -/
theorem movingSmoothPolynomialFactors_variation {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hL : L.natDegree ≤ 1) (hR : R.natDegree ≤ 1)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V)) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    ∃ S : Finset ℝ, S.card ≤ 2 ^ n ∧ ∀ (u : ℕ → ℝ), Monotone u → ∀ N : ℕ,
      rootCellCode S (u 0) = rootCellCode S (u (N - 1)) →
      discreteVariation (fun j => smoothPolynomialWeight
        (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip) (u j)) N ≤
      movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1) := by
  let F := movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi
  let H := movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
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
  · intro u hu N hcode
    apply (smoothPolynomialWeight_variation H S ?_ u hu N hcode).trans
      (movingSmoothPolynomialFactors_budget value T L R ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip)
    intro i r hr
    revert hr
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [H, movingSmoothPolynomialFactors, Fin.append_left]
      change r ∈ (F j).polynomial.derivative.roots → r ∈ S
      intro h
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Multiset.mem_toFinset.mpr h⟩
    · intro j
      simp only [H, movingSmoothPolynomialFactors, Fin.append_right]
      change r ∈ (movingNodeCutoffFactors value T L R φ G B D hB hD hφ hlip j).polynomial.derivative.roots → r ∈ S
      rw [movingNodeCutoffFactors_no_derivative_roots value T L R hL hR φ G B D hB hD hφ hlip j]
      simp

end Ostmann

end OAI
