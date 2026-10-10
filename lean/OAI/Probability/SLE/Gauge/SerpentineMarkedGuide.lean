import OAI.Probability.SLE.Gauge.SerpentineFiniteHeight
import OAI.Probability.SLE.Geometry.MarkedHookLocal

namespace OAI

/-! The explicit complete physical access guide from the final ribbon
tip, through the marked point, and then vertically to infinity. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

def terminalAccess (s : ℝ) (w : ℂ) (m : ℕ) (x : ℝ) (t : ℝ) : ℂ :=
  physicalFitChart s w m (guideCoordinate (fitCompletion s w m) x t)

def completeMarkedAccess (s : ℝ) (w : ℂ) (m : ℕ) (x : ℝ) : ℝ → ℂ :=
  appendMarkedHook (terminalAccess s w m x) (fitHighTime s w m) w
    (fitTerminalX s w) 2 (s / 20)

lemma terminalAccess_continuous {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) (x : ℝ) : Continuous (terminalAccess s w m x) := by
  have hp : Continuous (physicalFitChart s w m) :=
    continuous_const.mul (fitChart_continuous hs w hw hm)
  exact hp.comp (guideCoordinate_continuous _ _)

lemma terminalAccess_right {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    (hwr : 0 ≤ w.re) {m : ℕ} (hm : 0 < m) {x t : ℝ} (hx : |x| ≤ 1) (ht : 0 ≤ t) :
    w.re + s / 5 ≤ (terminalAccess s w m x t).re := by
  have hc := (fitCompletion_bounds hs w hw hm).1
  have hentry : 0 ≤ columnEntry 0 m (2 * m) := columnEntry_nonneg le_rfl _ _
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hA : fitEntry s w m < (guideCoordinate (fitCompletion s w m) x t).re := by
    rw [guideCoordinate_re]
    linarith
  have him := (guideCoordinate_im_bound (k := (fitCompletion s w m : ℝ)) (x := x) ht).trans hx
  have hh := physicalFitChart_array_right hs w hm him hA
  rw [abs_of_nonneg hwr] at hh
  exact by dsimp [terminalAccess]; linarith

lemma completeMarkedAccess_continuous {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (w : ℂ) (hw : s ≤ w.im) (hw1 : ‖w‖ ≤ 1) (hwr : 0 ≤ w.re)
    {m : ℕ} (hm : 0 < m) (x : ℝ) : Continuous (completeMarkedAccess s w m x) := by
  have hwi := (Complex.im_le_norm w).trans hw1
  apply appendMarkedHook_continuous _ (terminalAccess_continuous hs w hw hm x)
  · unfold fitTerminalX
    rw [abs_of_nonneg hwr]
    linarith
  · linarith
  · positivity
  · exact physicalFitChart_terminal_guide_endpoint hs hs1 w hw hw1 hm x

lemma completeMarkedAccess_injective {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (w : ℂ) (hw : s ≤ w.im) (hw1 : ‖w‖ ≤ 1) (hwr : 0 ≤ w.re)
    {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : |x| ≤ 1) :
    InjOn (completeMarkedAccess s w m x) (Ici 0) := by
  have hT := fitHighTime_large hs hs1 w hw hw1 hm
  have hwi := (Complex.im_le_norm w).trans hw1
  have hR : w.re < fitTerminalX s w := by
    unfold fitTerminalX
    rw [abs_of_nonneg hwr]
    linarith
  apply appendMarkedHook_injective _ (by linarith)
    ((physicalFitChart_terminal_guide_injective hs w hw hm x).mono Icc_subset_Ici_self)
    w hR (show w.im < (2 : ℝ) by linarith) (by positivity)
    (physicalFitChart_terminal_guide_endpoint hs hs1 w hw hw1 hm x)
  intro t ht
  refine ⟨physicalFitChart_terminal_guide_strict_height hs w hw hm x ht, Or.inr ?_⟩
  have hr := terminalAccess_right hs w hw hwr hm hx ht.1
  dsimp only [terminalAccess] at hr
  linarith

lemma completeMarkedAccess_zero {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (w : ℂ) (hw : s ≤ w.im) (hw1 : ‖w‖ ≤ 1) {m : ℕ} (hm : 0 < m) (x : ℝ) :
    completeMarkedAccess s w m x 0 = physicalFitChart s w m ((fitCompletion s w m : ℂ) + (x : ℂ) * Complex.I) := by
  have hT := fitHighTime_large hs hs1 w hw hw1 hm
  rw [completeMarkedAccess, appendMarkedHook, curveJoin_of_le (by linarith)]
  simp [terminalAccess, guideCoordinate]

lemma completeMarkedAccess_hits_marked {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (w : ℂ) (hw : s ≤ w.im) (hw1 : ‖w‖ ≤ 1) (hwr : 0 ≤ w.re)
    {m : ℕ} (hm : 0 < m) (x : ℝ) :
    ∃ t : ℝ, 0 < t ∧ completeMarkedAccess s w m x t = w := by
  have hT := fitHighTime_large hs hs1 w hw hw1 hm
  have hwi := (Complex.im_le_norm w).trans hw1
  have hR : w.re < fitTerminalX s w := by
    unfold fitTerminalX
    rw [abs_of_nonneg hwr]
    linarith
  refine ⟨fitHighTime s w m + ((fitTerminalX s w - w.re) + (2 - w.im)), by linarith, ?_⟩
  exact appendMarkedHook_passes_marked _ _ w hR (by linarith)

lemma completeMarkedAccess_norm_tendsto {s : ℝ} (hs : 0 < s)
    (w : ℂ) (hw1 : ‖w‖ ≤ 1) (hwr : 0 ≤ w.re) (m : ℕ) (x : ℝ) :
    Tendsto (fun t : ℝ => ‖completeMarkedAccess s w m x t‖) atTop atTop := by
  have hwi : w.im < 2 := lt_of_le_of_lt ((Complex.im_le_norm w).trans hw1) (by norm_num)
  have hR : w.re < fitTerminalX s w := by
    unfold fitTerminalX
    rw [abs_of_nonneg hwr]
    linarith
  let D := fitHighTime s w m + ((fitTerminalX s w - w.re) + (2 - w.im) + s / 20)
  have hlin : Tendsto (fun t : ℝ => t - D + w.im) atTop atTop := by
    simpa only [sub_eq_add_neg, add_assoc, id_eq] using
      tendsto_atTop_add_const_right atTop (-D + w.im) tendsto_id
  have him : Tendsto (fun t : ℝ => (completeMarkedAccess s w m x t).im) atTop atTop := by
    apply hlin.congr'
    filter_upwards [eventually_ge_atTop (D + 1)] with t ht
    have ht' : fitHighTime s w m < t := by dsimp only [D] at ht; linarith
    have hc : (fitTerminalX s w - w.re) + (2 - w.im) + s / 20 <
        t - fitHighTime s w m := by dsimp only [D] at ht; linarith
    rw [completeMarkedAccess, appendMarkedHook, curveJoin_of_gt ht',
      markedHook_tail w hwi (by positivity) hc]
    simp only [hookUp, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add]
    dsimp only [D]
    ring
  exact tendsto_atTop_mono (fun t => Complex.im_le_norm _) him

end SLEExactGauge.Serpentine

end

end OAI
