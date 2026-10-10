import OAI.NumberTheory.TwoPoint.Halasz.HalaszWeightedMeanSquare
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! Finite duality for sparse Dirichlet-polynomial samples.  The analytic
input is an explicit Gram-row sum, with no density-to-energy substitution. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical ComplexConjugate

lemma mrt_gram_synthesis {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Finset ι) (v : ι → E) (a : ι → ℂ)
    {B : ℝ} (hrow : ∀ i ∈ S, ∑ j ∈ S, ‖inner ℂ (v i) (v j)‖ ≤ B) :
    ‖∑ i ∈ S, a i • v i‖^2 ≤ B * ∑ i ∈ S, ‖a i‖^2 := by
  calc
    _ = (inner ℂ (∑ i ∈ S, a i • v i) (∑ i ∈ S, a i • v i)).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ ≤ ‖inner ℂ (∑ i ∈ S, a i • v i) (∑ i ∈ S, a i • v i)‖ := re_le_norm _
    _ = ‖∑ i ∈ S, ∑ j ∈ S, conj (a i) * a j * inner ℂ (v i) (v j)‖ := by
      simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_sum]
      rw [sum_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ‖conj (a i) * a j * inner ℂ (v i) (v j)‖ := by
      exact (norm_sum_le _ _).trans (sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ = ∑ i ∈ S, ∑ j ∈ S,
        (‖a i‖ * 1) * (‖a j‖ * 1) * ‖inner ℂ (v i) (v j)‖ := by
      simp only [norm_mul, norm_conj, mul_one]
    _ ≤ B * ∑ i ∈ S, ‖a i‖^2 := by
      simpa only [mul_one] using halasz_weighted_symmetric_row_bound S
        (fun i j => ‖inner ℂ (v i) (v j)‖) (fun _ => 1) (fun i => ‖a i‖) B
        (fun _ _ => by norm_num) (fun _ _ _ _ => norm_nonneg _)
        (fun i _ j _ => norm_inner_symm _ _) (by simpa only [one_mul] using hrow)

/-- Finite Bessel inequality with an absolute Gram-row bound. -/
theorem mrt_gram_analysis {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Finset ι) (v : ι → E) (u : E)
    {B : ℝ} (hB : 0 ≤ B) (hrow : ∀ i ∈ S, ∑ j ∈ S, ‖inner ℂ (v i) (v j)‖ ≤ B) :
    (∑ i ∈ S, ‖inner ℂ (v i) u‖^2) ≤ B * ‖u‖^2 := by
  let b := fun i => inner ℂ (v i) u
  let z := ∑ i ∈ S, b i • v i
  let A := ∑ i ∈ S, ‖b i‖^2
  have hA : 0 ≤ A := sum_nonneg (fun _ _ => sq_nonneg _)
  have hz : inner ℂ z u = (A : ℂ) := by
    dsimp only [z, A]
    rw [sum_inner]
    push_cast
    apply sum_congr rfl
    intro i _
    rw [inner_smul_left]
    exact conj_mul' (b i)
  have hc : A ≤ ‖z‖ * ‖u‖ := by
    calc
      A = ‖inner ℂ z u‖ := by rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
      _ ≤ _ := norm_inner_le_norm _ _
  have hz2 : ‖z‖^2 ≤ B*A := mrt_gram_synthesis S v b hrow
  have hc2 : A^2 ≤ ‖z‖^2 * ‖u‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hA hc 2
  have hprod := mul_le_mul_of_nonneg_right hz2 (sq_nonneg ‖u‖)
  by_cases hAz : A = 0
  · change A ≤ B * ‖u‖^2
    rw [hAz]
    exact mul_nonneg hB (sq_nonneg _)
  · change A ≤ B * ‖u‖^2
    have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    apply (mul_le_mul_iff_right₀ hApos).mp
    calc
      A * A = A^2 := by ring
      _ ≤ B * A * ‖u‖^2 := hc2.trans hprod
      _ = A * (B * ‖u‖^2) := by ring

/-- The Gram kernel is evaluated on the actual coefficient matrix. -/
theorem mrt_finite_matrix_gram {ι κ : Type*} (S : Finset ι) (K : Finset κ)
    (A : ι → κ → ℂ) (a : κ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, ‖∑ n ∈ K, A i n * conj (A j n)‖ ≤ B) :
    (∑ i ∈ S, ‖∑ n ∈ K, A i n * a n‖^2) ≤ B * ∑ n ∈ K, ‖a n‖^2 := by
  let v : ι → EuclideanSpace ℂ K := fun i => WithLp.toLp 2 (fun n => conj (A i n))
  let u : EuclideanSpace ℂ K := WithLp.toLp 2 (fun n => a n)
  have hinner (i j : ι) : inner ℂ (v i) (v j) = ∑ n ∈ K, A i n * conj (A j n) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply']
    change (∑ n : K, conj (conj (A i n)) * conj (A j n)) = _
    simp only [conj_conj]
    exact sum_coe_sort K (fun n => A i n * conj (A j n))
  have heval (i : ι) : inner ℂ (v i) u = ∑ n ∈ K, A i n * a n := by
    simp only [PiLp.inner_apply, RCLike.inner_apply']
    change (∑ n : K, conj (conj (A i n)) * a n) = _
    simp only [conj_conj]
    exact sum_coe_sort K (fun n => A i n * a n)
  have hnorm : ‖u‖^2 = ∑ n ∈ K, ‖a n‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ n : K, ‖a n‖^2) = _
    exact sum_coe_sort K (fun n => ‖a n‖^2)
  have hr : ∀ i ∈ S, ∑ j ∈ S, ‖inner ℂ (v i) (v j)‖ ≤ B := by
    simpa only [hinner] using hrow
  simpa only [heval, hnorm] using mrt_gram_analysis S v u hB hr

end TwoPointCorrelations

end OAI
