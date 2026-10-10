import OAI.Probability.InvariantIsing.Gaussian.GaussianCompactVariance

namespace OAI

/-! Compact scalar cutoffs preserving the exact Lipschitz constant. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace InvariantIsing

def gaussianCone {d : ℕ} (L : ℝ≥0) (R : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  max ((L : ℝ)*(R-‖x‖)) 0

def gaussianConeCutoff {d : ℕ} (L : ℝ≥0) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  max (-gaussianCone L R x) (min (f x) (gaussianCone L R x))

lemma gaussianCone_nonneg {d : ℕ} (L : ℝ≥0) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ gaussianCone L R x := le_max_right _ _

lemma gaussianCone_lipschitz {d : ℕ} (L : ℝ≥0) (R : ℝ) :
    LipschitzWith L (gaussianCone (d := d) L R) := by
  have h : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin d) => (L : ℝ)*(R-‖x‖)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have he : (L : ℝ)*(R-‖x‖)-(L : ℝ)*(R-‖y‖) = (L : ℝ)*(‖y‖-‖x‖) := by ring
    rw [he, abs_mul, abs_of_nonneg L.coe_nonneg]
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, dist_comm y x] using
      (lipschitzWith_one_norm (E := EuclideanSpace ℝ (Fin d))).dist_le_mul y x
  exact h.max_const 0

lemma gaussianConeCutoff_lipschitz {d : ℕ} {L : ℝ≥0} {R : ℝ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f) :
    LipschitzWith L (gaussianConeCutoff L R f) := by
  unfold gaussianConeCutoff
  simpa only [Pi.neg_apply, max_self] using
    (gaussianCone_lipschitz (d := d) L R).neg.max (hf.min (gaussianCone_lipschitz L R))

lemma gaussianConeCutoff_zero {d : ℕ} (L : ℝ≥0) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hx : R ≤ ‖x‖) : gaussianConeCutoff L R f x = 0 := by
  have hc : gaussianCone L R x = 0 :=
    max_eq_right (mul_nonpos_of_nonneg_of_nonpos L.coe_nonneg (sub_nonpos.mpr hx))
  simp only [gaussianConeCutoff, hc, neg_zero, max_eq_left (min_le_right _ _)]

lemma gaussianConeCutoff_compact {d : ℕ} (L : ℝ≥0) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : HasCompactSupport (gaussianConeCutoff L R f) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R)
  intro x hx
  by_contra hn
  have he : R ≤ ‖x‖ := le_of_lt (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn)
  exact hx (gaussianConeCutoff_zero L R f x he)

lemma gaussianConeCutoff_norm_le {d : ℕ} (L : ℝ≥0) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖gaussianConeCutoff L R f x‖ ≤ ‖f x‖ := by
  have ha := gaussianCone_nonneg L R x
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  unfold gaussianConeCutoff
  by_cases hf : 0 ≤ f x
  · have hlo : 0 ≤ max (-gaussianCone L R x) (min (f x) (gaussianCone L R x)) :=
      (le_min hf ha).trans (le_max_right _ _)
    rw [abs_of_nonneg hlo, abs_of_nonneg hf]
    exact max_le (by linarith) (min_le_left _ _)
  · have hf' : f x ≤ 0 := (lt_of_not_ge hf).le
    rw [min_eq_left (hf'.trans ha), abs_of_nonpos (max_le (by linarith) hf'), abs_of_nonpos hf']
    exact neg_le_neg (le_max_right _ _)

lemma gaussianConeCutoff_eq {d : ℕ} {L : ℝ≥0} {R : ℝ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f) (h0 : f 0 = 0)
    (x : EuclideanSpace ℝ (Fin d)) (hx : 2*‖x‖ ≤ R) :
    gaussianConeCutoff L R f x = f x := by
  have hb : |f x| ≤ (L : ℝ)*‖x‖ := by
    simpa only [h0, dist_zero_right, Real.norm_eq_abs] using hf.dist_le_mul x 0
  have hh : (L : ℝ)*‖x‖ ≤ (L : ℝ)*(R-‖x‖) :=
    mul_le_mul_of_nonneg_left (by linarith) L.coe_nonneg
  have ha : |f x| ≤ gaussianCone L R x := hb.trans (hh.trans (le_max_left _ _))
  unfold gaussianConeCutoff
  rw [min_eq_left ((le_abs_self _).trans ha), max_eq_right]
  linarith [neg_le_abs (f x)]

end InvariantIsing

end

end OAI
