import OAI.Probability.SLE.Gauge.SerpentineMarkedClearance

namespace OAI

/-! The actual last front is on the terminal vertical piece. Its access
guide reaches height two before the explicit marked hook is attached. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

def fitEntry (s : ℝ) (w : ℂ) (m : ℕ) : ℝ :=
  connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)

def fitCompletion (s : ℝ) (w : ℂ) (m : ℕ) : ℕ := completionStep (fitEntry s w m) m

def fitTerminalX (s : ℝ) (w : ℂ) : ℝ := |w.re| + s / 4 + s / 200

def fitTerminalHeight (s : ℝ) (w : ℂ) (m : ℕ) : ℝ :=
  ribbonWidth (halfHeight s) m *
    (fitY s w m + fitCompletion s w m - fitEntry s w m - columnEntry 0 m (2 * m))

def fitHighTime (s : ℝ) (w : ℂ) (m : ℕ) : ℝ :=
  (2 - fitTerminalHeight s w m) / ribbonWidth (halfHeight s) m

lemma fitCompletion_bounds {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) :
    fitEntry s w m + columnEntry 0 m (2 * m) + 200 * m ≤ fitCompletion s w m ∧
    (fitCompletion s w m : ℝ) < fitEntry s w m + columnEntry 0 m (2 * m) + 200 * m + 1 := by
  have hA : 0 ≤ fitEntry s w m := by
    have h := fit_entry_lower hs w hw hm
    exact le_trans (by unfold fitHeight; positivity) h
  have hlo := Nat.le_ceil (columnEntry (fitEntry s w m) m (2 * m) + 200 * m)
  have hhi := Nat.ceil_lt_add_one
    (add_nonneg (columnEntry_nonneg hA m (2 * m)) (by positivity : (0 : ℝ) ≤ 200 * m))
  change _ ≤ (fitCompletion s w m : ℝ) at hlo
  change (fitCompletion s w m : ℝ) < _ at hhi
  have he : columnEntry (fitEntry s w m) m (2 * m) =
      fitEntry s w m + columnEntry 0 m (2 * m) := by simp [columnEntry]
  rw [he] at hlo hhi
  exact ⟨hlo, hhi⟩

lemma fit_scaledY {s : ℝ} (hs : 0 < s) (w : ℂ) {m : ℕ} (hm : 0 < m) :
    ribbonWidth (halfHeight s) m * fitY s w m = w.im - s / 200 := by
  unfold fitY halfHeight
  exact mul_div_cancel₀ _ (fit_width_pos hs hm).ne'

lemma fitTerminalHeight_bounds {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) :
    w.im + s / 200 ≤ fitTerminalHeight s w m ∧
    fitTerminalHeight s w m < w.im + s / 200 + ribbonWidth (halfHeight s) m := by
  obtain ⟨hlo, hhi⟩ := fitCompletion_bounds hs w hw hm
  have hℓ := fit_width_pos hs hm
  have hl := mul_le_mul_of_nonneg_left hlo hℓ.le
  have hh := mul_lt_mul_of_pos_left hhi hℓ
  have hY := fit_scaledY hs w hm
  have hmℓ := fit_width_mul hs hm
  unfold fitTerminalHeight
  constructor <;> nlinarith

lemma physicalFitChart_terminal {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) {z : ℂ} (hz : (fitCompletion s w m : ℝ) ≤ z.re) :
    physicalFitChart s w m z =
      ((fitTerminalX s w - ribbonWidth (halfHeight s) m * z.im : ℝ) : ℂ) +
      ((fitTerminalHeight s w m + ribbonWidth (halfHeight s) m *
        (z.re - fitCompletion s w m) : ℝ) : ℂ) * Complex.I := by
  have hthreshold : fitEntry s w m + columnEntry 0 m (2 * m) + 1 ≤ z.re := by
    have h := (fitCompletion_bounds hs w hw hm).1
    have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  obtain ⟨hσ, hT⟩ := complete_linear_tail m (fitHeight m) (fitRadius m)
    (fitX s w m) (fitY s w m) hthreshold
  have hX := fit_scaledX hs w hm
  have hmℓ := fit_width_mul hs hm
  change ((ribbonWidth (halfHeight s) m : ℂ) *
    (completeSpine m _ _ _ _ z.re + (z.im : ℂ) * Complex.I * completeTangent m _ _ _ _ z.re)) = _
  rw [hσ, hT]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add]
  · unfold fitTerminalX
    nlinarith
  · unfold fitTerminalHeight fitEntry
    ring

lemma fitHighTime_large {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (w : ℂ)
    (hw : s ≤ w.im) (hw1 : ‖w‖ ≤ 1) {m : ℕ} (hm : 0 < m) :
    1 < fitHighTime s w m := by
  have hheight := (fitTerminalHeight_bounds hs w hw hm).2
  have hwi := (Complex.im_le_norm w).trans hw1
  have hwidth := fit_width_le hs hm
  rw [fitHighTime, lt_div_iff₀ (fit_width_pos hs hm)]
  nlinarith

/-- Exact physical formula for the tapered terminal access guide. -/
lemma physicalFitChart_terminal_guide {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    physicalFitChart s w m (guideCoordinate (fitCompletion s w m) x t) =
      ((fitTerminalX s w - ribbonWidth (halfHeight s) m * x * max (1 - 4 * t) 0 : ℝ) : ℂ) +
      ((fitTerminalHeight s w m + ribbonWidth (halfHeight s) m * t : ℝ) : ℂ) * Complex.I := by
  rw [physicalFitChart_terminal hs w hw hm (by rw [guideCoordinate_re]; linarith),
    guideCoordinate_re, guideCoordinate_im]
  push_cast
  ring

lemma physicalFitChart_terminal_guide_endpoint {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (w : ℂ) (hw : s ≤ w.im) (hw1 : ‖w‖ ≤ 1) {m : ℕ} (hm : 0 < m) (x : ℝ) :
    physicalFitChart s w m (guideCoordinate (fitCompletion s w m) x (fitHighTime s w m)) =
      (fitTerminalX s w : ℂ) + (2 : ℂ) * Complex.I := by
  have hT := fitHighTime_large hs hs1 w hw hw1 hm
  rw [physicalFitChart_terminal_guide hs w hw hm x (by linarith),
    max_eq_right (by linarith : 1 - 4 * fitHighTime s w m ≤ 0), mul_zero, sub_zero]
  have he : fitTerminalHeight s w m + ribbonWidth (halfHeight s) m * fitHighTime s w m = 2 := by
    unfold fitHighTime
    rw [mul_div_cancel₀ _ (fit_width_pos hs hm).ne']
    ring
  rw [he]
  norm_num

lemma physicalFitChart_terminal_guide_height {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) (x : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (fitHighTime s w m)) :
    (physicalFitChart s w m (guideCoordinate (fitCompletion s w m) x t)).im ≤ 2 := by
  rw [physicalFitChart_terminal_guide hs w hw hm x ht.1]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  have h := mul_le_mul_of_nonneg_left ht.2 (fit_width_pos hs hm).le
  unfold fitHighTime at h
  rw [mul_div_cancel₀ _ (fit_width_pos hs hm).ne'] at h
  linarith

lemma physicalFitChart_terminal_guide_strict_height {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) (x : ℝ) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) (fitHighTime s w m)) :
    (physicalFitChart s w m (guideCoordinate (fitCompletion s w m) x t)).im < 2 := by
  rw [physicalFitChart_terminal_guide hs w hw hm x ht.1]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  have h := mul_lt_mul_of_pos_left ht.2 (fit_width_pos hs hm)
  unfold fitHighTime at h
  rw [mul_div_cancel₀ _ (fit_width_pos hs hm).ne'] at h
  linarith

lemma physicalFitChart_terminal_guide_injective {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) (x : ℝ) :
    InjOn (fun t => physicalFitChart s w m (guideCoordinate (fitCompletion s w m) x t)) (Ici 0) := by
  intro t ht u hu he
  have him := congrArg Complex.im he
  dsimp only at him
  rw [physicalFitChart_terminal_guide hs w hw hm x ht,
    physicalFitChart_terminal_guide hs w hw hm x hu] at him
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at him
  nlinarith [fit_width_pos hs hm]

end SLEExactGauge.Serpentine

end

end OAI
