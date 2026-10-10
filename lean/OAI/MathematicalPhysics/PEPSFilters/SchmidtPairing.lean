import Mathlib

namespace OAI

/-! Quadratic and weighted row-column estimates for Schmidt coefficients. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
open Real Set

lemma clipped_log_lipschitz {b c p q : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hp : 0 < p) (hq : 0 < q) :
    |Real.log (max b (p/c)) - Real.log (max b (q/c))| ≤ |Real.log p - Real.log q| := by
  have hlog (x : ℝ) (hx : 0 < x) : Real.log (max b (x/c)) = max (Real.log b) (Real.log x - Real.log c) := by
    rcases le_total b (x/c) with h | h
    · rw [max_eq_right h, Real.log_div hx.ne' hc.ne', max_eq_right]
      rw [← Real.log_div hx.ne' hc.ne']
      exact Real.log_le_log hb h
    · rw [max_eq_left h, max_eq_left]
      rw [← Real.log_div hx.ne' hc.ne']
      exact Real.log_le_log (div_pos hx hc) h
  rw [hlog p hp, hlog q hq, max_comm (Real.log b), max_comm (Real.log b)]
  convert abs_max_sub_max_le_abs (Real.log p - Real.log c) (Real.log q - Real.log c) (Real.log b) using 1
  congr 1
  ring

lemma convexOn_sinh_nonneg : ConvexOn ℝ (Set.Ici 0) Real.sinh := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ici 0) Real.continuous_sinh.continuousOn
    Real.differentiable_sinh.differentiableOn
  intro x hx y hy hxy
  simp only [Real.deriv_sinh]
  apply Real.cosh_strictMonoOn.monotoneOn
  · exact interior_subset hx
  · exact interior_subset hy
  · exact hxy

lemma sinh_mul_le {a y : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hy : 0 ≤ y) :
    Real.sinh (a*y) ≤ a * Real.sinh y := by
  have h := convexOn_sinh_nonneg.2 (show (0 : ℝ) ∈ Set.Ici 0 by simp) hy
    (sub_nonneg.mpr ha1) ha (by ring : (1-a)+a=1)
  simpa only [smul_eq_mul, mul_zero, zero_add, Real.sinh_zero, add_zero] using h

lemma cosh_mul_sub_one_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (y : ℝ) :
    Real.cosh (a*y) - 1 ≤ a^2 * (Real.cosh y - 1) := by
  have hs := sinh_mul_le ha ha1 (by positivity : 0 ≤ |y|/2)
  have hp : 0 ≤ Real.sinh (a*(|y|/2)) := Real.sinh_nonneg_iff.mpr (by positivity)
  have hq : 0 ≤ a*Real.sinh (|y|/2) := mul_nonneg ha (Real.sinh_nonneg_iff.mpr (by positivity))
  have hs2 := mul_self_le_mul_self hp hs
  have h1 := Real.cosh_two_mul (a*(|y|/2))
  have h2 := Real.cosh_two_mul (|y|/2)
  rw [Real.cosh_sq] at h1 h2
  have ht : 2 * (a*(|y|/2)) = |a*y| := by rw [abs_mul, abs_of_nonneg ha]; ring
  rw [ht, Real.cosh_abs] at h1
  have hu : 2 * (|y|/2) = |y| := by ring
  rw [hu, Real.cosh_abs] at h2
  nlinarith [hs2]

lemma sqrt_mul_cosh_half_log {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Real.sqrt (p*q) * Real.cosh ((Real.log p - Real.log q)/2) = (p+q)/2 := by
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hl : (Real.log p - Real.log q)/2 = Real.log (Real.sqrt p) - Real.log (Real.sqrt q) := by
    rw [Real.log_sqrt hp.le, Real.log_sqrt hq.le]
    ring
  rw [hl, Real.cosh_eq, Real.sqrt_mul hp.le, Real.exp_sub, Real.exp_log hsp, Real.exp_log hsq]
  rw [neg_sub, Real.exp_sub, Real.exp_log hsq, Real.exp_log hsp]
  field_simp
  nlinarith [Real.sq_sqrt hp.le, Real.sq_sqrt hq.le]

lemma quadratic_coefficient {a p q l k : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hp : 0 < p) (hq : 0 < q) (hl : 0 < l) (hk : 0 < k)
    (hr : |Real.log l - Real.log k| ≤ a/2 * |Real.log p - Real.log q|) :
    0 ≤ Real.sqrt (p*q) * (Real.cosh (Real.log (l/k)) - 1) ∧
    Real.sqrt (p*q) * (Real.cosh (Real.log (l/k)) - 1) ≤ a^2/2 * (p+q) := by
  constructor
  · exact mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr (Real.one_le_cosh _))
  · have hc : Real.cosh (Real.log (l/k)) ≤ Real.cosh (a*((Real.log p-Real.log q)/2)) := by
      apply Real.cosh_le_cosh.mpr
      rw [Real.log_div hl.ne' hk.ne', abs_mul, abs_of_nonneg ha, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
      convert hr using 1
      ring
    have hcos := cosh_mul_sub_one_le ha ha1 ((Real.log p-Real.log q)/2)
    have hcc : Real.cosh (Real.log (l/k)) - 1 ≤ a^2 * (Real.cosh ((Real.log p-Real.log q)/2) - 1) := by linarith
    have hm := mul_le_mul_of_nonneg_left hcc (Real.sqrt_nonneg (p*q))
    have he := sqrt_mul_cosh_half_log hp hq
    have hs : 0 ≤ a^2 * Real.sqrt (p*q) := mul_nonneg (sq_nonneg a) (Real.sqrt_nonneg _)
    nlinarith [hm]

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

open scoped BigOperators InnerProductSpace
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] in
lemma orthonormal_column_sq (A : E →L[ℂ] E) (e : ι → E)
    (he : Orthonormal ℂ e) (k : ι) :
    ∑ i, ‖inner ℂ (e i) (A (e k))‖^2 ≤ ‖A‖^2 := by
  have h := he.sum_inner_products_le (A (e k)) (s := Finset.univ)
  have hb : ‖A (e k)‖ ≤ ‖A‖ := by simpa only [he.norm_eq_one, mul_one] using A.le_opNorm (e k)
  exact h.trans (pow_le_pow_left₀ (norm_nonneg _) hb 2)

lemma orthonormal_row_sq (A : E →L[ℂ] E) (e : ι → E)
    (he : Orthonormal ℂ e) (i : ι) :
    ∑ k, ‖inner ℂ (e i) (A (e k))‖^2 ≤ ‖A‖^2 := by
  have hh (k : ι) : ‖inner ℂ (e i) (A (e k))‖ =
      ‖inner ℂ (e k) ((ContinuousLinearMap.adjoint A) (e i))‖ := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact norm_inner_symm _ _
  simp_rw [hh]
  simpa only [ContinuousLinearMap.adjoint.norm_map] using
    orthonormal_column_sq (ContinuousLinearMap.adjoint A) e he i

lemma row_column_product (A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (e : ι → E) (f : ι → F) (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f) :
    (∀ i, ∑ k, ‖inner ℂ (e i) (A (e k)) * inner ℂ (f i) (B (f k))‖ ≤ ‖A‖*‖B‖) ∧
    (∀ k, ∑ i, ‖inner ℂ (e i) (A (e k)) * inner ℂ (f i) (B (f k))‖ ≤ ‖A‖*‖B‖) := by
  have aux (x y : ι → ℝ) (hx : ∑ i, x i ^ 2 ≤ ‖A‖^2)
      (hy : ∑ i, y i ^ 2 ≤ ‖B‖^2) : ∑ i, x i * y i ≤ ‖A‖*‖B‖ := by
    apply (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ x y).trans
    apply mul_le_mul
    · exact (Real.sqrt_le_sqrt hx).trans_eq (Real.sqrt_sq (norm_nonneg _))
    · exact (Real.sqrt_le_sqrt hy).trans_eq (Real.sqrt_sq (norm_nonneg _))
    · exact Real.sqrt_nonneg _
    · exact norm_nonneg _
  constructor
  · intro i
    simp_rw [norm_mul]
    exact aux _ _ (orthonormal_row_sq A e he i) (orthonormal_row_sq B f hf i)
  · intro k
    simp_rw [norm_mul]
    exact aux _ _ (orthonormal_column_sq A e he k) (orthonormal_column_sq B f hf k)

lemma weighted_row_column {d : ι → ι → ℝ} {C : ℝ}
    (hd : (∀ i, ∑ k, d i k ≤ C) ∧ (∀ k, ∑ i, d i k ≤ C))
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    ∑ i, ∑ k, (p i + p k) * d i k ≤ 2*C := by
  calc
    _ = (∑ i, p i * ∑ k, d i k) + (∑ k, p k * ∑ i, d i k) := by
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      rw [Finset.sum_comm (f := fun i k => p k * d i k)]
    _ ≤ (∑ i, p i * C) + (∑ k, p k * C) := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hd.1 i) (hp i))
      · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hd.2 i) (hp i))
    _ = 2*C := by rw [← Finset.sum_mul, hs]; ring

lemma weighted_product_bound (A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (e : ι → E) (f : ι → F) (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    ∑ i, ∑ k, (p i + p k) * ‖inner ℂ (e i) (A (e k)) * inner ℂ (f i) (B (f k))‖
       ≤ 2 * (‖A‖ * ‖B‖) :=
  weighted_row_column (row_column_product A B e f he hf) p hp hs
end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
open scoped BigOperators
open Real
variable {ι : Type*} [Fintype ι]

lemma hermitian_pairing (w h : ι → ι → ℝ) (l : ι → ℝ)
    (hw : ∀ i k, w i k = w k i) (hh : ∀ i k, h i k = h k i) (hl : ∀ i, 0 < l i) :
    ∑ i, ∑ k, w i k * (l i / l k - 1) * h i k =
    ∑ i, ∑ k, w i k * (Real.cosh (Real.log (l i/l k)) - 1) * h i k := by
  have hs : ∑ i, ∑ k, w i k * (l k / l i - 1) * h i k =
      ∑ i, ∑ k, w i k * (l i / l k - 1) * h i k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    rw [hw i k, hh i k]
  have ht : ∑ i, ∑ k, w i k * (Real.cosh (Real.log (l i/l k)) - 1) * h i k =
      ((∑ i, ∑ k, w i k * (l i/l k - 1) * h i k) +
       (∑ i, ∑ k, w i k * (l k/l i - 1) * h i k)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [Real.cosh_log (div_pos (hl i) (hl k)), inv_div]
    ring
  rw [ht, hs]
  ring

lemma quadratic_coefficient_nonneg {a p q l k : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hl : 0 < l) (hk : 0 < k)
    (hr : 0 < p → 0 < q → |Real.log l - Real.log k| ≤ a/2 * |Real.log p - Real.log q|) :
    0 ≤ Real.sqrt (p*q) * (Real.cosh (Real.log (l/k)) - 1) ∧
    Real.sqrt (p*q) * (Real.cosh (Real.log (l/k)) - 1) ≤ a^2/2 * (p+q) := by
  rcases hp.eq_or_lt with hp | hp
  · subst p
    simp only [zero_mul, Real.sqrt_zero, zero_add]
    exact ⟨le_rfl, by positivity⟩
  rcases hq.eq_or_lt with hq | hq
  · subst q
    simp only [mul_zero, Real.sqrt_zero, zero_mul, add_zero]
    exact ⟨le_rfl, by positivity⟩
  exact quadratic_coefficient ha ha1 hp hq hl hk (hr hp hq)

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma quadratic_product_sum (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1)
    (l : ι → ℝ) (hl : ∀ i, 0 < l i)
    (hr : ∀ i k, 0 < p i → 0 < p k →
      |Real.log (l i) - Real.log (l k)| ≤ a/2 * |Real.log (p i) - Real.log (p k)|)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (e : ι → E) (f : ι → F) (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f) :
    ∑ i, ∑ k, (Real.sqrt (p i*p k) * (Real.cosh (Real.log (l i/l k)) - 1)) *
      ‖inner ℂ (e i) (A (e k)) * inner ℂ (f i) (B (f k))‖ ≤ a^2 * (‖A‖*‖B‖) := by
  calc
    _ ≤ ∑ i, ∑ k, (a^2/2 * (p i+p k)) *
        ‖inner ℂ (e i) (A (e k)) * inner ℂ (f i) (B (f k))‖ := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro k _
      exact mul_le_mul_of_nonneg_right
        (quadratic_coefficient_nonneg ha ha1 (hp i) (hp k) (hl i) (hl k) (hr i k)).2
        (norm_nonneg _)
    _ = a^2/2 * (∑ i, ∑ k, (p i+p k) *
        ‖inner ℂ (e i) (A (e k)) * inner ℂ (f i) (B (f k))‖) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ a^2/2 * (2*(‖A‖*‖B‖)) :=
      mul_le_mul_of_nonneg_left (weighted_product_bound A B e f he hf p hp hps) (by positivity)
    _ = _ := by ring

lemma one_crossing_schmidt_bound {ν : Type*} [Fintype ν]
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1)
    (l : ι → ℝ) (hl : ∀ i, 0 < l i)
    (hr : ∀ i k, 0 < p i → 0 < p k →
      |Real.log (l i) - Real.log (l k)| ≤ a/2 * |Real.log (p i) - Real.log (p k)|)
    (A : ν → E →L[ℂ] E) (B : ν → F →L[ℂ] F)
    (e : ι → E) (f : ι → F) (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f)
    (h : ι → ι → ℂ) (hsym : ∀ i k, h i k = star (h k i))
    (hexp : ∀ i k, h i k = ∑ z, inner ℂ (e i) (A z (e k)) * inner ℂ (f i) (B z (f k))) :
    |∑ i, ∑ k, Real.sqrt (p i*p k) * (l i/l k - 1) * (h i k).re| ≤
      a^2 * ∑ z, ‖A z‖*‖B z‖ := by
  rw [hermitian_pairing (fun i k => Real.sqrt (p i*p k)) (fun i k => (h i k).re) l
    (fun i k => by rw [mul_comm]) (fun i k => by rw [hsym i k]; rfl) hl]
  let c := fun i k => Real.sqrt (p i*p k) * (Real.cosh (Real.log (l i/l k)) - 1)
  have hc (i k) : 0 ≤ c i k := (quadratic_coefficient_nonneg ha ha1 (hp i) (hp k) (hl i) (hl k) (hr i k)).1
  calc
    _ ≤ ∑ i, ∑ k, c i k * ‖h i k‖ := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum; intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum; intro k _
      rw [abs_mul, abs_of_nonneg (hc i k)]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (hc i k)
    _ ≤ ∑ i, ∑ k, c i k * ∑ z, ‖inner ℂ (e i) (A z (e k)) * inner ℂ (f i) (B z (f k))‖ := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro k _
      apply mul_le_mul_of_nonneg_left _ (hc i k)
      rw [hexp]
      exact norm_sum_le _ _
    _ = ∑ z, ∑ i, ∑ k, c i k * ‖inner ℂ (e i) (A z (e k)) * inner ℂ (f i) (B z (f k))‖ := by
      simp only [Finset.mul_sum]
      trans ∑ i, ∑ z, ∑ k, c i k * ‖inner ℂ (e i) (A z (e k)) * inner ℂ (f i) (B z (f k))‖
      · apply Finset.sum_congr rfl; intro i _
        exact Finset.sum_comm
      · exact Finset.sum_comm
    _ ≤ ∑ z, a^2 * (‖A z‖*‖B z‖) :=
      Finset.sum_le_sum (fun z _ => quadratic_product_sum a ha ha1 p hp hps l hl hr (A z) (B z) e f he hf)
    _ = _ := (Finset.mul_sum ..).symm
end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

end

end OAI
