import OAI.Probability.InvariantIsing.Spectral.SpectralEnergy

namespace OAI

/-! The continuous nonnegative right derivative of the finite spectral
R-transform. Its extension at zero is the spectral variance; the constant
extension of `finiteR` to negative arguments is not differentiated there. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def cavityRDerivative (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (x : ℝ) : ℝ :=
  ∑ a, projectedResolventDerivative rho lam hrho hsum a x *
    (lam a - finiteR rho lam hrho hsum x) ^ 2

lemma cavityRDerivative_nonneg (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (x : ℝ) : 0 ≤ cavityRDerivative rho lam hrho hsum x :=
  Finset.sum_nonneg (fun a _ => mul_nonneg
    (projectedResolventDerivative_pos rho lam hrho hsum a x).le (sq_nonneg _))

lemma continuous_cavityRDerivative (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) : Continuous (cavityRDerivative rho lam hrho hsum) := by
  apply continuous_finsetSum
  intro a _
  exact (continuous_projectedResolventDerivative rho lam hrho hsum a).mul
    ((continuous_const.sub (continuous_finiteR rho lam hrho hsum)).pow 2)

lemma cavityRDerivative_zero (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) :
    cavityRDerivative rho lam hrho hsum 0 =
      ∑ a, rho a * (lam a - ∑ b, rho b * lam b) ^ 2 := by
  simp only [cavityRDerivative, projectedResolventDerivative, finiteR,
    lt_self_iff_false, ite_false]

theorem cavityRDerivative_eq_deriv (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) {x : ℝ} (hx : 0 < x) :
    cavityRDerivative rho lam hrho hsum x = deriv (finiteR rho lam hrho hsum) x := by
  let b := finiteInverse rho lam hrho hsum x
  let M := finiteSecondResolvent rho lam b
  have hspec := finiteInverse_spec rho lam hrho hsum hx
  have hM : M ≠ 0 := (finiteSecondResolvent_pos (fun a => (hrho a).le) hsum hspec.1).ne'
  have hgap (a : ι) : b - lam a ≠ 0 := (sub_pos.mpr (hspec.1 a)).ne'
  have hterm (a : ι) : projectedResolventDerivative rho lam hrho hsum a x *
      (lam a - finiteR rho lam hrho hsum x) ^ 2 =
        ((rho a / (b - lam a) ^ 2) / x ^ 2 -
          (2 / x) * (rho a / (b - lam a)) + rho a) / M := by
    simp only [projectedResolventDerivative, finiteR, ite_eq_left hx]
    change rho a / (M * (b - lam a) ^ 2) * (lam a - (b - 1 / x)) ^ 2 = _
    field_simp [hM, hgap a, hx.ne']
    ring
  calc
    cavityRDerivative rho lam hrho hsum x =
        (M / x ^ 2 - (2 / x) * x + 1) / M := by
      unfold cavityRDerivative
      simp_rw [hterm]
      rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_div, ← Finset.mul_sum, hsum]
      change (M / x ^ 2 - (2 / x) * finiteResolvent rho lam b + 1) / M = _
      rw [hspec.2]
    _ = -1 / M + 1 / x ^ 2 := by field_simp [hM, hx.ne']; ring
    _ = deriv (finiteR rho lam hrho hsum) x :=
      (hasStrictDerivAt_finiteR rho lam hrho hsum hx).hasDerivAt.deriv.symm

theorem cavityRDerivative_le (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) {K : ℝ} (_hK : 0 ≤ K)
    (hlam : ∀ a, |lam a| ≤ K) (x : ℝ) :
    cavityRDerivative rho lam hrho hsum x ≤ 4 * K ^ 2 := by
  have hR := finiteR_mem_interval rho lam hrho hsum
    (fun a => (abs_le.mp (hlam a)).1) (fun a => (abs_le.mp (hlam a)).2) x
  calc
    cavityRDerivative rho lam hrho hsum x ≤
        ∑ a, projectedResolventDerivative rho lam hrho hsum a x * (4 * K ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _
        (projectedResolventDerivative_pos rho lam hrho hsum a x).le
      have ha := abs_le.mp (hlam a)
      have hlow : -2 * K ≤ lam a - finiteR rho lam hrho hsum x := by linarith
      have hupp : lam a - finiteR rho lam hrho hsum x ≤ 2 * K := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hupp)]
    _ = 4 * K ^ 2 := by rw [← Finset.sum_mul, sum_projectedResolventDerivative, one_mul]

/-- The ordinary FTC includes the right endpoint derivative extension at
zero while using derivatives only at strictly positive interior points. -/
theorem integral_cavityRDerivative (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, cavityRDerivative rho lam hrho hsum x) =
      finiteR rho lam hrho hsum b - finiteR rho lam hrho hsum a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (continuous_finiteR rho lam hrho hsum).continuousOn
  · intro x hx
    have hpos : 0 < x := ha.trans_lt hx.1
    have h := (hasStrictDerivAt_finiteR rho lam hrho hsum hpos).hasDerivAt
    rw [← h.deriv, ← cavityRDerivative_eq_deriv rho lam hrho hsum hpos] at h
    exact h
  · exact (continuous_cavityRDerivative rho lam hrho hsum).intervalIntegrable a b

end InvariantIsing

end

end OAI
