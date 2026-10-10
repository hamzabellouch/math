import OAI.Probability.SLE.Gauge.SerpentineEscape
import OAI.Probability.SLE.Gauge.SerpentineShadow

namespace OAI

/-! Concrete normalized connector parameters for the dense-visit layout.
All constants depend only on the fixed positive angle lower bound. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

def fitHeight (m : ℕ) : ℝ := 2500 * m

def fitRadius (m : ℕ) : ℝ := 625 * m

def fitX (s : ℝ) (w : ℂ) (m : ℕ) : ℝ :=
  (|w.re| + s / 4 - halfHeight s) / ribbonWidth (halfHeight s) m

def fitY (s : ℝ) (w : ℂ) (m : ℕ) : ℝ :=
  (w.im - halfHeight s) / ribbonWidth (halfHeight s) m

def fitEntryBound (s : ℝ) : ℝ := 40000 / s + 10000 + 1000 * Real.pi

lemma fit_width_pos {s : ℝ} (hs : 0 < s) {m : ℕ} (hm : 0 < m) :
    0 < ribbonWidth (halfHeight s) m := by
  apply ribbonWidth_pos (by unfold halfHeight; positivity) hm

lemma fit_width_eq (s : ℝ) (m : ℕ) :
    ribbonWidth (halfHeight s) m = s / (20000 * m) := by
  unfold ribbonWidth halfHeight
  ring

lemma fit_width_mul {s : ℝ} (_hs : 0 < s) {m : ℕ} (hm : 0 < m) :
    ribbonWidth (halfHeight s) m * m = s / 20000 := by
  rw [fit_width_eq]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

lemma fitX_eq {s : ℝ} (hs : 0 < s) (w : ℂ) {m : ℕ} (hm : 0 < m) :
    fitX s w m = (20000 * |w.re| / s + 4900) * m := by
  unfold fitX
  rw [fit_width_eq]
  unfold halfHeight
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp [hs.ne', hm']
  ring

lemma fitY_eq {s : ℝ} (hs : 0 < s) (w : ℂ) {m : ℕ} (hm : 0 < m) :
    fitY s w m = (20000 * w.im / s - 100) * m := by
  unfold fitY
  rw [fit_width_eq]
  unfold halfHeight
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp [hs.ne', hm']
  ring

lemma fitX_lower {s : ℝ} (hs : 0 < s) (w : ℂ) {m : ℕ} (hm : 0 < m) :
    4900 * (m : ℝ) ≤ fitX s w m := by
  rw [fitX_eq hs w hm]
  have h := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20000) (abs_nonneg w.re)) hs.le
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

lemma fitY_lower {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im) {m : ℕ} (hm : 0 < m) :
    19900 * (m : ℝ) ≤ fitY s w m := by
  rw [fitY_eq hs w hm]
  have h : (20000 : ℝ) ≤ 20000 * w.im / s := (le_div_iff₀ hs).mpr (by nlinarith)
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

lemma fitX_upper {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : ‖w‖ ≤ 1) {m : ℕ} (hm : 0 < m) :
    fitX s w m ≤ (20000 / s + 4900) * m := by
  rw [fitX_eq hs w hm]
  have hre : |w.re| ≤ 1 := (Complex.abs_re_le_norm w).trans hw
  have h : 20000 * |w.re| / s ≤ 20000 / s := by
    apply div_le_div_of_nonneg_right _ hs.le
    nlinarith
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg m)

lemma fitY_upper {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : ‖w‖ ≤ 1) {m : ℕ} (hm : 0 < m) :
    fitY s w m ≤ (20000 / s) * m := by
  rw [fitY_eq hs w hm]
  have him : w.im ≤ 1 := (Complex.im_le_norm w).trans hw
  have h : 20000 * w.im / s ≤ 20000 / s := by
    apply div_le_div_of_nonneg_right _ hs.le
    nlinarith
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg m)

/-- The fixed numerical parameters satisfy all proved global embedding
and local ribbon estimates, with ample strict separation. -/
theorem fit_parameters {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) :
    50 ≤ fitRadius m ∧ 2 * fitRadius m < fitX s w m ∧
      fitHeight m + 2 * fitRadius m + 1 + 300 * m < fitY s w m ∧
      4 ≤ fitHeight m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx := fitX_lower hs w hm
  have hy := fitY_lower hs w hw hm
  dsimp only [fitRadius, fitHeight]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma fitEntryBound_pos {s : ℝ} (hs : 0 < s) : 0 < fitEntryBound s := by
  unfold fitEntryBound
  positivity

lemma connectorEntry_eq (H r X Y : ℝ) :
    connectorEntry H r X Y = Real.pi * r + X + Y - 4 * r := by
  unfold connectorEntry connectorFourth connectorThird connectorSecond quarterLength
  ring

lemma fit_entry_upper {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : ‖w‖ ≤ 1)
    {m : ℕ} (hm : 0 < m) :
    connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m) ≤ fitEntryBound s * m := by
  have hx := fitX_upper hs w hw hm
  have hy := fitY_upper hs w hw hm
  rw [connectorEntry_eq]
  dsimp only [fitRadius, fitEntryBound]
  have hdiv : 40000 / s = 2 * (20000 / s) := by ring
  rw [hdiv]
  nlinarith [mul_nonneg Real.pi_pos.le (Nat.cast_nonneg (α := ℝ) m)]

lemma fit_entry_lower {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) :
    fitHeight m ≤ connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m) := by
  have hx := fitX_lower hs w hm
  have hy := fitY_lower hs w hw hm
  have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [connectorEntry_eq]
  dsimp only [fitHeight, fitRadius]
  nlinarith [Real.pi_pos]

lemma fit_completion_quadratic {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : ‖w‖ ≤ 1)
    (hwy : s ≤ w.im) {m : ℕ} (hm : 0 < m) :
    (completionStep (connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)) m : ℝ) ≤
      (fitEntryBound s + 601 + 100 * Real.pi) * (m : ℝ) ^ 2 := by
  apply completionStep_quadratic_bound
  · exact (by unfold fitHeight; positivity : (0 : ℝ) ≤ fitHeight m).trans (fit_entry_lower hs w hwy hm)
  · exact (fitEntryBound_pos hs).le
  · exact hm
  · exact fit_entry_upper hs w hw hm

end SLEExactGauge.Serpentine

end

end OAI
