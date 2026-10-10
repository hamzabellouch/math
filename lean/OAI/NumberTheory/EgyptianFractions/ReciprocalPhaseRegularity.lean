import OAI.NumberTheory.EgyptianFractions.ForwardDifference

namespace OAI
noncomputable section
open Set
open scoped ContDiff

namespace Problem337

/-- Every derivative of a smooth forward difference stays smooth on the
positive half-line. -/
theorem forwardDifference_iteratedDeriv_contDiffOn (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) :
    ContDiffOn ℝ ∞ (iteratedDeriv k (forwardDifference hs f)) (Ioi 0) := by
  induction k with
  | zero => simpa using forwardDifference_contDiffOn hs hhs hf
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

/-- Local regularity in the exact pointwise form used by a second derivative
test. No global smoothness at zero is asserted. -/
theorem forwardDifference_iteratedDeriv_hasDerivAt (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (iteratedDeriv k (forwardDifference hs f))
      (iteratedDeriv (k + 1) (forwardDifference hs f) x) x := by
  rw [iteratedDeriv_succ]
  exact ((forwardDifference_iteratedDeriv_contDiffOn k hs hhs hf).contDiffAt
    (isOpen_Ioi.mem_nhds hx)).differentiableAt (by simp) |>.hasDerivAt

/-- Pointwise derivatives of every order of a differenced reciprocal phase. -/
theorem reciprocal_forwardDifference_hasDerivAt (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) (Z : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (iteratedDeriv k (forwardDifference hs (fun y => Z / y)))
      (iteratedDeriv (k + 1) (forwardDifference hs (fun y => Z / y)) x) x := by
  apply forwardDifference_iteratedDeriv_hasDerivAt k hs hhs _ hx
  exact contDiffOn_const.div contDiffOn_id (fun y hy => ne_of_gt hy)

/-- Paired first and second derivatives for the continuous second derivative test. -/
theorem reciprocal_forwardDifference_second_derivative_data (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) (Z : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (forwardDifference hs (fun y => Z / y))
      (iteratedDeriv 1 (forwardDifference hs (fun y => Z / y)) x) x ∧
    HasDerivAt (iteratedDeriv 1 (forwardDifference hs (fun y => Z / y)))
      (iteratedDeriv 2 (forwardDifference hs (fun y => Z / y)) x) x := by
  constructor
  · simpa using reciprocal_forwardDifference_hasDerivAt 0 hs hhs Z hx
  · exact reciprocal_forwardDifference_hasDerivAt 1 hs hhs Z hx

end Problem337

end

end OAI
