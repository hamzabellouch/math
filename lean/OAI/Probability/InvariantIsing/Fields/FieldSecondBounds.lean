import OAI.Probability.InvariantIsing.Fields.FieldSecondFamily

namespace OAI

/-! Local bounds for the explicit first and second derivatives of the
affine Gaussian mark in the finite scalar recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing
namespace FieldSecondFamily

variable {I : Set ℝ} (F : FieldSecondFamily I)

def shiftedMixed (a v u : ℝ) (p : ℝ × ℝ) : ℝ :=
  F.TX (p.1, p.2 + Real.sqrt (a + v * p.1) * u) +
    F.XX (p.1, p.2 + Real.sqrt (a + v * p.1) * u) *
      (fieldAmplitudeSlope a v p.1 * u)

def shiftedSecond (a v u : ℝ) (p : ℝ × ℝ) : ℝ :=
  F.TT (p.1, p.2 + Real.sqrt (a + v * p.1) * u) +
    2 * F.TX (p.1, p.2 + Real.sqrt (a + v * p.1) * u) *
      (fieldAmplitudeSlope a v p.1 * u) +
    F.XX (p.1, p.2 + Real.sqrt (a + v * p.1) * u) *
      (fieldAmplitudeSlope a v p.1 * u) ^ 2 +
    F.X (p.1, p.2 + Real.sqrt (a + v * p.1) * u) *
      (fieldAmplitudeCurvature a v p.1 * u)

lemma shiftedTangent_bound (a v u : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I)
    {R : ℝ} (hR : 0 ≤ R) (hc : |fieldAmplitudeSlope a v p.1| ≤ R) :
    |F.shiftedTangent a v u p| ≤ (F.KT + F.KX * R) * (1 + |u|) := by
  have hT0 : 0 ≤ F.KT := (abs_nonneg _).trans (F.bT (p.1, 0) hp)
  have hX0 := F.kx_nonneg
  unfold shiftedTangent
  calc
    _ ≤ |F.T _| + |F.X _ * (fieldAmplitudeSlope a v p.1 * u)| := abs_add_le _ _
    _ ≤ F.KT + F.KX * (R * |u|) := by
      rw [abs_mul, abs_mul]
      gcongr
      · exact F.bT _ hp
      · exact F.bX _
    _ ≤ (F.KT + F.KX * R) * (1 + |u|) := by
      nlinarith [mul_nonneg hT0 (abs_nonneg u), mul_nonneg hX0 hR]

lemma shiftedMixed_bound (a v u : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I)
    {R : ℝ} (hR : 0 ≤ R) (hc : |fieldAmplitudeSlope a v p.1| ≤ R) :
    |F.shiftedMixed a v u p| ≤ (F.KTX + F.KXX * R) * (1 + |u|) := by
  have hT0 : 0 ≤ F.KTX := (abs_nonneg _).trans (F.bTX (p.1, 0) hp)
  have hX0 : 0 ≤ F.KXX := (abs_nonneg _).trans (F.bXX (0, 0))
  unfold shiftedMixed
  calc
    _ ≤ |F.TX _| + |F.XX _ * (fieldAmplitudeSlope a v p.1 * u)| := abs_add_le _ _
    _ ≤ F.KTX + F.KXX * (R * |u|) := by
      rw [abs_mul, abs_mul]
      gcongr
      · exact F.bTX _ hp
      · exact F.bXX _
    _ ≤ (F.KTX + F.KXX * R) * (1 + |u|) := by
      nlinarith [mul_nonneg hT0 (abs_nonneg u), mul_nonneg hX0 hR]

lemma shiftedSecond_bound (a v u : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I)
    {R D : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hc : |fieldAmplitudeSlope a v p.1| ≤ R)
    (hd : |fieldAmplitudeCurvature a v p.1| ≤ D) :
    |F.shiftedSecond a v u p| ≤
      (F.KTT + 2 * F.KTX * R + F.KXX * R ^ 2 + F.KX * D) * (1 + |u|) ^ 2 := by
  have hTT0 : 0 ≤ F.KTT := (abs_nonneg _).trans (F.bTT (p.1, 0) hp)
  have hTX0 : 0 ≤ F.KTX := (abs_nonneg _).trans (F.bTX (p.1, 0) hp)
  have hXX0 : 0 ≤ F.KXX := (abs_nonneg _).trans (F.bXX (0, 0))
  have hX0 := F.kx_nonneg
  have h1 : 1 ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u]
  have hu : |u| ≤ (1 + |u|) ^ 2 := by nlinarith [sq_nonneg |u|, abs_nonneg u]
  have hu2 : |u| ^ 2 ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u]
  let w : ℝ × ℝ := (p.1, p.2 + Real.sqrt (a + v * p.1) * u)
  have hTT := F.bTT w hp
  have hTX := F.bTX w hp
  have hXX := F.bXX w
  have hX := F.bX w
  unfold shiftedSecond
  calc
    _ ≤ |F.TT w| + |2 * F.TX w * (fieldAmplitudeSlope a v p.1 * u)| +
        |F.XX w * (fieldAmplitudeSlope a v p.1 * u) ^ 2| +
        |F.X w * (fieldAmplitudeCurvature a v p.1 * u)| := by
      refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ F.KTT + 2 * F.KTX * (R * |u|) + F.KXX * (R * |u|) ^ 2 +
        F.KX * (D * |u|) := by
      simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      gcongr
    _ = F.KTT * 1 + (2 * F.KTX * R) * |u| +
        (F.KXX * R ^ 2) * |u| ^ 2 + (F.KX * D) * |u| := by ring
    _ ≤ F.KTT * (1 + |u|) ^ 2 + (2 * F.KTX * R) * (1 + |u|) ^ 2 +
        (F.KXX * R ^ 2) * (1 + |u|) ^ 2 + (F.KX * D) * (1 + |u|) ^ 2 := by
      gcongr
    _ = _ := by ring

end FieldSecondFamily
end InvariantIsing

end

end OAI
