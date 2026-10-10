import OAI.Analysis.FreeEntropy.MonomialSeries

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter
namespace FiniteEntropySeparation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem polynomialL2_ext {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) {x y : H}
    (hx : x ∈ polynomialL2 τ X) (hy : y ∈ polynomialL2 τ X)
    (h : ∀ w, inner ℂ x (wordEval X w τ.vacuum) = inner ℂ y (wordEval X w τ.vacuum)) : x = y := by
  have hmem := (polynomialL2 τ X).sub_mem hx hy
  have hker : polynomialL2 τ X ≤ (innerSL ℂ (x - y)).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨w,rfl⟩
      change inner ℂ (x-y) (wordEval X w τ.vacuum) = 0
      rw [inner_sub_left, h w, sub_self]
    · exact (innerSL ℂ (x-y)).isClosed_ker
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (hker hmem))

 theorem polynomialL2_eq_projection {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) {x y : H}
    (hx : x ∈ polynomialL2 τ X)
    (h : ∀ w, inner ℂ x (wordEval X w τ.vacuum) = inner ℂ y (wordEval X w τ.vacuum)) :
    x = (polynomialL2 τ X).starProjection y := by
  apply polynomialL2_ext τ X hx ((polynomialL2 τ X).starProjection_apply_mem y)
  intro w
  have hp := (polynomialL2 τ X).starProjection_inner_eq_zero y
    (wordEval X w τ.vacuum) (wordVector_mem_polynomialL2 τ X w)
  rw [inner_sub_left, ← h w] at hp
  exact sub_eq_zero.mp hp

 theorem norm_le_of_polynomial_testing {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) {x y : H}
    (hx : x ∈ polynomialL2 τ X)
    (h : ∀ w, inner ℂ x (wordEval X w τ.vacuum) = inner ℂ y (wordEval X w τ.vacuum)) :
    ‖x‖ ≤ ‖y‖ := by
  rw [polynomialL2_eq_projection τ X hx h]
  exact (polynomialL2 τ X).norm_starProjection_apply_le y

 theorem conjugate_residual_norm_sq {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (i : Fin n) (v : ℝ)
    (hv : ‖X i τ.vacuum‖ ^ 2 = v) :
    ‖X i τ.vacuum - (v : ℂ) • ξ i‖ ^ 2 = v ^ 2 * ‖ξ i‖ ^ 2 - v := by
  have hp : inner ℂ (X i τ.vacuum) (ξ i) = 1 := by
    rw [← inner_conj_symm, conjugate_coordinate_pairing τ hξ i]
    simp
  rw [norm_sub_sq (𝕜 := ℂ), hv, inner_smul_right, hp, mul_one, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  change v - 2 * v + v ^ 2 * ‖ξ i‖ ^ 2 = _
  ring

theorem fisher_residual_bound {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (v : Fin n → ℝ) (u : ℝ) (hu : 0 < u)
    (hv : ∀ i, ‖X i τ.vacuum‖ ^ 2 = v i) (hvu : ∀ i, u ≤ v i)
    (R : Fin n → H)
    (hR : ∀ i w, inner ℂ (X i τ.vacuum) (wordEval X w τ.vacuum) -
        (v i : ℂ) * derivativeMoment τ X i w = inner ℂ (R i) (wordEval X w τ.vacuum)) :
    0 ≤ (∑ i, ‖ξ i‖ ^ 2) - (∑ i, (v i)⁻¹) ∧
      (∑ i, ‖ξ i‖ ^ 2) - (∑ i, (v i)⁻¹) ≤ (u ^ 2)⁻¹ * ∑ i, ‖R i‖ ^ 2 := by
  have hvp (i : Fin n) : 0 < v i := hu.trans_le (hvu i)
  have hl (i : Fin n) : (v i)⁻¹ ≤ ‖ξ i‖ ^ 2 := by
    simpa only [hv i, one_div] using conjugate_norm_sq_lower τ hξ i
  have hn (i : Fin n) : ‖X i τ.vacuum - (v i : ℂ) • ξ i‖ ≤ ‖R i‖ := by
    apply norm_le_of_polynomial_testing τ X
    · apply (polynomialL2 τ X).sub_mem
      · simpa [wordEval] using wordVector_mem_polynomialL2 τ X [i]
      · exact (polynomialL2 τ X).smul_mem _ (hξ i).1
    · intro w
      simpa only [inner_sub_left, inner_smul_left, map_ofNat, Complex.conj_ofReal,
        (hξ i).2 w] using hR i w
  have hi (i : Fin n) : ‖ξ i‖ ^ 2 - (v i)⁻¹ ≤ (u ^ 2)⁻¹ * ‖R i‖ ^ 2 := by
    have hs : (v i) ^ 2 * ‖ξ i‖ ^ 2 - v i ≤ ‖R i‖ ^ 2 := by
      rw [← conjugate_residual_norm_sq τ hξ i (v i) (hv i)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hn i) 2
    have huv : u ^ 2 ≤ (v i) ^ 2 := pow_le_pow_left₀ hu.le (hvu i) 2
    have hd : 0 ≤ ‖ξ i‖ ^ 2 - (v i)⁻¹ := sub_nonneg.mpr (hl i)
    have hmult := mul_le_mul_of_nonneg_right huv hd
    rw [mul_comm ((u ^ 2)⁻¹), ← div_eq_mul_inv]
    apply (le_div_iff₀ (sq_pos_of_pos hu)).mpr
    have ha : (v i) ^ 2 * (v i)⁻¹ = v i := by
      rw [pow_two, mul_assoc, mul_inv_cancel₀ (hvp i).ne', mul_one]
    calc
      _ = u ^ 2 * (‖ξ i‖ ^ 2 - (v i)⁻¹) := mul_comm _ _
      _ ≤ (v i) ^ 2 * (‖ξ i‖ ^ 2 - (v i)⁻¹) := hmult
      _ = (v i) ^ 2 * ‖ξ i‖ ^ 2 - v i := by rw [mul_sub, ha]
      _ ≤ _ := hs
  constructor
  · exact sub_nonneg.mpr (Finset.sum_le_sum (fun i _ => hl i))
  · rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hi i

end FiniteEntropySeparation

end

end OAI
