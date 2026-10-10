import OAI.Algebra.DepthFive.FiniteOperator
import OAI.Algebra.DepthFive.LowerSchedule
import OAI.Algebra.DepthFive.AnalyticParameters
import OAI.Algebra.DepthFive.BinomialRatios

namespace OAI

/-! Common, concrete data for the two sides of the IMM rank comparison. -/

noncomputable section

namespace Problem335.LowerParameters

/-- The source dimension for the configured bidegree rank measure. -/
def rankDimension (n : ℕ) : ℝ :=
  (homogeneousDim (v n) (a n) : ℝ) * (homogeneousDim (u n) (b n) : ℝ)

/-- The common path-count and occupation-mean factor in the two trace moments. -/
def rankMomentScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ (n - 1) * ((a n : ℝ) / (v n : ℝ)) ^ k n *
    (1 + (b n : ℝ) / (u n : ℝ)) ^ m n

/-- The actual rank measure, extended by zero outside the range where the
balanced schedule is used. The small values do not enter the eventual bounds. -/
def rankData (n : ℕ) (p : MvPolynomial (Fin n × Fin n × Fin n) ℂ) : ℝ :=
  if hn : 4 ≤ n then
    (bidegreeRank (fun x : Fin n × Fin n × Fin n => balancedLayer hn x.1)
      (a n) (b n) (k n) (m n) p : ℝ)
  else 0

theorem rankData_eq {n : ℕ} (hn : 4 ≤ n)
    (p : MvPolynomial (Fin n × Fin n × Fin n) ℂ) :
    rankData n p =
      (bidegreeRank (fun x : Fin n × Fin n × Fin n => balancedLayer hn x.1)
        (a n) (b n) (k n) (m n) p : ℝ) := by
  simp [rankData, hn]

theorem rankData_nonneg (n : ℕ)
    (p : MvPolynomial (Fin n × Fin n × Fin n) ℂ) : 0 ≤ rankData n p := by
  unfold rankData
  split_ifs <;> positivity

theorem rankDimension_nonneg (n : ℕ) : 0 ≤ rankDimension n := by
  unfold rankDimension
  positivity

theorem rankDimension_pos {n : ℕ} (hn : 4 ≤ n) : 0 < rankDimension n := by
  have hv : 0 < homogeneousDim (v n) (a n) :=
    homogeneousDim_pos (v_pos hn) (a n)
  have hu : 0 < homogeneousDim (u n) (b n) :=
    homogeneousDim_pos (u_pos hn) (b n)
  unfold rankDimension
  positivity

theorem rankMomentScale_pos {n : ℕ} (hn : 4 ≤ n) : 0 < rankMomentScale n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos hn
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos hn
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos hn
  unfold rankMomentScale
  positivity

end Problem335.LowerParameters

end

end OAI
