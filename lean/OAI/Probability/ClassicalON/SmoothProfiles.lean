import OAI.Probability.ClassicalON.DyadicFourier

namespace OAI

noncomputable section
open Set Function
open scoped Topology ContDiff

namespace ClassicalON

def thetaBump : ContDiffBump (0 : ℝ) := ⟨4/3, 5/3, by norm_num, by norm_num⟩
def outerBump : ContDiffBump (0 : ℝ) := ⟨7/4, 15/8, by norm_num, by norm_num⟩
def innerBump : ContDiffBump (0 : ℝ) := ⟨9/8, 5/4, by norm_num, by norm_num⟩

def squareTheta (z : ℝ × ℝ) : ℝ := thetaBump z.1 * thetaBump z.2

def squareCutoff (z : ℝ × ℝ) : ℝ :=
  outerBump z.1 * outerBump z.2 * (1-innerBump z.1*innerBump z.2)

def squareGradient (m : Bool) (z : ℝ × ℝ) : ℝ :=
  if m then thetaBump z.1 * deriv thetaBump z.2 else deriv thetaBump z.1 * thetaBump z.2

def squareProfile (m sign : Bool) (z : ℝ × ℝ) : ℝ :=
  if sign then (squareCutoff z-squareGradient m z)/2 else
    (squareCutoff z+squareGradient m z)/2

theorem thetaBump_one {x : ℝ} (hx : |x| ≤ 4/3) : thetaBump x = 1 := by
  apply thetaBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, thetaBump] using hx

theorem thetaBump_zero {x : ℝ} (hx : 5/3 ≤ |x|) : thetaBump x = 0 := by
  apply thetaBump.zero_of_le_dist
  simpa [Real.dist_eq, thetaBump] using hx

theorem thetaBump_deriv_zero_inner {x : ℝ} (hx : |x| ≤ 4/3) : deriv thetaBump x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [thetaBump_one hx]
  exact thetaBump.le_one

theorem thetaBump_deriv_zero_outer {x : ℝ} (hx : 5/3 ≤ |x|) : deriv thetaBump x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [thetaBump_zero hx]
  exact thetaBump.nonneg

theorem outerBump_one {x : ℝ} (hx : |x| ≤ 7/4) : outerBump x = 1 := by
  apply outerBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, outerBump] using hx

theorem outerBump_zero {x : ℝ} (hx : 15/8 ≤ |x|) : outerBump x = 0 := by
  apply outerBump.zero_of_le_dist
  simpa [Real.dist_eq, outerBump] using hx

theorem innerBump_one {x : ℝ} (hx : |x| ≤ 9/8) : innerBump x = 1 := by
  apply innerBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, innerBump] using hx

theorem innerBump_zero {x : ℝ} (hx : 5/4 ≤ |x|) : innerBump x = 0 := by
  apply innerBump.zero_of_le_dist
  simpa [Real.dist_eq, innerBump] using hx

theorem squareTheta_one (z : ℝ × ℝ) (hx : |z.1| ≤ 1) (hy : |z.2| ≤ 1) :
    squareTheta z = 1 := by
  rw [squareTheta, thetaBump_one (by linarith), thetaBump_one (by linarith), mul_one]

theorem squareTheta_zero (z : ℝ × ℝ) (h : 2 ≤ |z.1| ∨ 2 ≤ |z.2|) :
    squareTheta z = 0 := by
  rcases h with hx | hy
  · simp [squareTheta, thetaBump_zero (by linarith : 5/3 ≤ |z.1|)]
  · simp [squareTheta, thetaBump_zero (by linarith : 5/3 ≤ |z.2|)]

theorem squareCutoff_gradient (m : Bool) (z : ℝ × ℝ) :
    squareCutoff z * squareGradient m z = squareGradient m z := by
  cases m
  · simp only [squareGradient, Bool.false_eq_true, ↓reduceIte]
    by_cases hg : deriv thetaBump z.1 = 0
    · simp [hg]
    by_cases ht : thetaBump z.2 = 0
    · simp [ht]
    have hx : 4/3 < |z.1| ∧ |z.1| < 5/3 := by
      constructor
      · exact lt_of_not_ge (fun h => hg (thetaBump_deriv_zero_inner h))
      · exact lt_of_not_ge (fun h => hg (thetaBump_deriv_zero_outer h))
    have hy : |z.2| < 5/3 := lt_of_not_ge (fun h => ht (thetaBump_zero h))
    simp [squareCutoff, outerBump_one (by linarith : |z.1| ≤ 7/4),
      outerBump_one (by linarith : |z.2| ≤ 7/4), innerBump_zero (by linarith : 5/4 ≤ |z.1|)]
  · simp only [squareGradient, ↓reduceIte]
    by_cases hg : deriv thetaBump z.2 = 0
    · simp [hg]
    by_cases ht : thetaBump z.1 = 0
    · simp [ht]
    have hy : 4/3 < |z.2| ∧ |z.2| < 5/3 := by
      constructor
      · exact lt_of_not_ge (fun h => hg (thetaBump_deriv_zero_inner h))
      · exact lt_of_not_ge (fun h => hg (thetaBump_deriv_zero_outer h))
    have hx : |z.1| < 5/3 := lt_of_not_ge (fun h => ht (thetaBump_zero h))
    simp [squareCutoff, outerBump_one (by linarith : |z.1| ≤ 7/4),
      outerBump_one (by linarith : |z.2| ≤ 7/4), innerBump_zero (by linarith : 5/4 ≤ |z.2|)]

theorem squareProfile_squares (m : Bool) (z : ℝ × ℝ) :
    squareProfile m false z ^ 2 - squareProfile m true z ^ 2 = squareGradient m z := by
  simp only [squareProfile, Bool.false_eq_true, ↓reduceIte]
  have h := squareCutoff_gradient m z
  nlinarith

theorem squareProfile_zero_inner (m s : Bool) (z : ℝ × ℝ)
    (hx : |z.1| ≤ 1) (hy : |z.2| ≤ 1) : squareProfile m s z = 0 := by
  have hc : squareCutoff z = 0 := by
    simp [squareCutoff, innerBump_one (by linarith : |z.1| ≤ 9/8),
      innerBump_one (by linarith : |z.2| ≤ 9/8)]
  have hg : squareGradient m z = 0 := by
    cases m <;> simp [squareGradient,
      thetaBump_deriv_zero_inner (by linarith : |z.1| ≤ 4/3),
      thetaBump_deriv_zero_inner (by linarith : |z.2| ≤ 4/3)]
  cases s <;> simp [squareProfile, hc, hg]

theorem squareProfile_zero_outer (m s : Bool) (z : ℝ × ℝ)
    (h : 2 ≤ |z.1| ∨ 2 ≤ |z.2|) : squareProfile m s z = 0 := by
  have hc : squareCutoff z = 0 := by
    rcases h with hx | hy
    · simp [squareCutoff, outerBump_zero (by linarith : 15/8 ≤ |z.1|)]
    · simp [squareCutoff, outerBump_zero (by linarith : 15/8 ≤ |z.2|)]
  have hg : squareGradient m z = 0 := by
    rcases h with hx | hy
    · cases m <;> simp [squareGradient,
        thetaBump_zero (by linarith : 5/3 ≤ |z.1|),
        thetaBump_deriv_zero_outer (by linarith : 5/3 ≤ |z.1|)]
    · cases m <;> simp [squareGradient,
        thetaBump_zero (by linarith : 5/3 ≤ |z.2|),
        thetaBump_deriv_zero_outer (by linarith : 5/3 ≤ |z.2|)]
  cases s <;> simp [squareProfile, hc, hg]

theorem squareTheta_contDiff : ContDiff ℝ ∞ squareTheta := by
  exact (thetaBump.contDiff.comp contDiff_fst).mul (thetaBump.contDiff.comp contDiff_snd)

theorem squareCutoff_contDiff : ContDiff ℝ ∞ squareCutoff := by
  apply ((outerBump.contDiff.comp contDiff_fst).mul (outerBump.contDiff.comp contDiff_snd)).mul
  exact contDiff_const.sub ((innerBump.contDiff.comp contDiff_fst).mul (innerBump.contDiff.comp contDiff_snd))

theorem squareGradient_contDiff (m : Bool) : ContDiff ℝ ∞ (squareGradient m) := by
  have hd : ContDiff ℝ ∞ (deriv thetaBump) := (contDiff_infty_iff_deriv.mp (thetaBump.contDiff : ContDiff ℝ ∞ thetaBump)).2
  cases m
  · exact (hd.comp contDiff_fst).mul (thetaBump.contDiff.comp contDiff_snd)
  · exact (thetaBump.contDiff.comp contDiff_fst).mul (hd.comp contDiff_snd)

theorem squareProfile_contDiff (m s : Bool) : ContDiff ℝ ∞ (squareProfile m s) := by
  cases s
  · exact (squareCutoff_contDiff.add (squareGradient_contDiff m)).div_const 2
  · exact (squareCutoff_contDiff.sub (squareGradient_contDiff m)).div_const 2

theorem squareProfile_compact (m s : Bool) : HasCompactSupport (squareProfile m s) := by
  apply HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (-2:ℝ) 2 ×ˢ Icc (-2:ℝ) 2))
  intro z hz
  apply squareProfile_zero_outer
  by_contra h
  push Not at h
  apply hz
  constructor <;> constructor <;> nlinarith [abs_le.mp h.1.le, abs_le.mp h.2.le]

end ClassicalON

end

end OAI
