import Mathlib

namespace OAI

/-! Normalization of the local geometric occupation moments in the four-path
trace expansion. Missing derivative occupations are handled by local-polynomial
identities, preserving the repeated-coordinate second moment rather than
treating it as a product of independent moments. -/

noncomputable section
open scoped BigOperators

namespace Problem335.LocalMomentWeights

/-- `isD` denotes the nonzero-difference pairing. `same` is relevant only in
its complementary pairing, where the two selected coordinates may coincide. -/
def moment (isV isD same : Bool) (A B : ℝ) : ℝ :=
  if isV then
    if isD then A * (A + 1) else if same then 2 * A ^ 2 + A else A ^ 2
  else
    if isD then B * (B + 1) else if same then 2 * B ^ 2 + 3 * B + 1
      else (B + 1) ^ 2

/-- The square of the first-moment factor at a layer. -/
def scale (isV : Bool) (A B : ℝ) : ℝ :=
  if isV then A ^ 2 else (B + 1) ^ 2

/-- The exact local weights after division by the first-moment square. -/
def weight (isV isD same : Bool) (alpha beta : ℝ) : ℝ :=
  if isV then
    if isD then alpha⁻¹ else 1 + if same then alpha⁻¹ else 0
  else
    if isD then beta else 1 + if same then beta else 0

lemma scale_pos (isV : Bool) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) :
    0 < scale isV A B := by
  cases isV <;> simp only [scale, Bool.false_eq_true, ↓reduceIte] <;> positivity

lemma weight_nonneg (isV isD same : Bool) {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 ≤ beta) : 0 ≤ weight isV isD same alpha beta := by
  cases isV <;> cases isD <;> cases same <;> simp [weight] <;> positivity

/-- Repeated-coordinate geometric second moments give the additional term
`alpha⁻¹` or `beta` exactly. -/
theorem moment_eq_scale_mul_weight (isV isD same : Bool) {A B : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) :
    moment isV isD same A B =
      scale isV A B * weight isV isD same (A / (A + 1)) (B / (B + 1)) := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hAp : A + 1 ≠ 0 := by linarith
  have hBp : B + 1 ≠ 0 := by linarith
  cases isV <;> cases isD <;> cases same <;>
    simp [moment, scale, weight] <;> field_simp <;> ring

lemma moment_div_scale (isV isD same : Bool) {A B : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) :
    moment isV isD same A B / scale isV A B =
      weight isV isD same (A / (A + 1)) (B / (B + 1)) := by
  rw [moment_eq_scale_mul_weight _ _ _ hA hB]
  exact mul_div_cancel_left₀ _ (scale_pos isV hA hB).ne'

/-- The normalized means agree with the original degree/cardinality ratios. -/
lemma mean_ratio {a v : ℝ} (hv : 0 < v) (ha : 0 ≤ a) :
    (a / v) / (a / v + 1) = a / (a + v) := by
  have hv0 : v ≠ 0 := ne_of_gt hv
  have hap : a + v ≠ 0 := by linarith
  field_simp

/-- A pointwise normalization can be factored out of the entire layer product. -/
theorem prod_moment_eq {ι : Type*} (s : Finset ι)
    (isV isD same : ι → Bool) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) :
    (∏ i ∈ s, moment (isV i) (isD i) (same i) A B) =
      (∏ i ∈ s, scale (isV i) A B) *
      ∏ i ∈ s, weight (isV i) (isD i) (same i) (A / (A + 1)) (B / (B + 1)) := by
  simp_rw [moment_eq_scale_mul_weight _ _ _ hA hB]
  exact Finset.prod_mul_distrib

/-- The product of the local normalization factors is exactly `mu^2`. -/
theorem prod_scale_eq {ι : Type*} (s : Finset ι) (isV : ι → Bool) (A B : ℝ) :
    (∏ i ∈ s, scale (isV i) A B) =
      (A ^ (s.filter (fun i => isV i = true)).card *
        (B + 1) ^ (s.filter (fun i => isV i = false)).card) ^ 2 := by
  classical
  simp only [scale]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hfilter : s.filter (fun i => ¬isV i = true) =
      s.filter (fun i => isV i = false) := by
    ext i
    cases isV i <;> simp
  rw [hfilter, mul_pow]
  congr 1 <;> rw [← pow_mul, ← pow_mul] <;> congr 1 <;> omega

/-- Full local-weight normalization for a fixed four-path pairing pattern. -/
theorem prod_moment_eq_mu_sq_mul {ι : Type*} (s : Finset ι)
    (isV isD same : ι → Bool) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) :
    (∏ i ∈ s, moment (isV i) (isD i) (same i) A B) =
      (A ^ (s.filter (fun i => isV i = true)).card *
        (B + 1) ^ (s.filter (fun i => isV i = false)).card) ^ 2 *
      ∏ i ∈ s, weight (isV i) (isD i) (same i) (A / (A + 1)) (B / (B + 1)) := by
  rw [prod_moment_eq s isV isD same hA hB, prod_scale_eq]

end Problem335.LocalMomentWeights

end

end OAI
