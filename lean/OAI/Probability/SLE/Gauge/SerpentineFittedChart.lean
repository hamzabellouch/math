import OAI.Probability.SLE.Gauge.SerpentineParameters
import OAI.Probability.SLE.Gauge.SerpentineUpperHalfPlane
import OAI.Probability.SLE.Gauge.SerpentineRetainedStrips

namespace OAI

/-! The concrete normalized chart, with the universal local constants
used by the ribbon iteration. The physical width is recorded separately. -/

noncomputable section
open Set Metric
open scoped NNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

def fitSpine (s : ℝ) (w : ℂ) (m : ℕ) : ℝ → ℂ :=
  completeSpine m (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)

def fitTangent (s : ℝ) (w : ℂ) (m : ℕ) : ℝ → ℂ :=
  completeTangent m (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)

def fitChart (s : ℝ) (w : ℂ) (m : ℕ) : ℂ → ℂ :=
  normalRibbon (fitSpine s w m) (fitTangent s w m)

def positiveCenter (s : ℝ) (w : ℂ) : ℂ :=
  ((|w.re| + s / 4 : ℝ) : ℂ) + (w.im : ℂ) * Complex.I

lemma fitChart_continuous {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) : Continuous (fitChart s w m) := by
  obtain ⟨hr, hx, hy, _⟩ := fit_parameters hs w hw hm
  exact complete_normal_continuous m hr hx (by linarith [Nat.cast_nonneg (α := ℝ) m])

lemma fitChart_injective {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) : InjOn (fitChart s w m) closedRibbon := by
  obtain ⟨hr, hx, hy, _⟩ := fit_parameters hs w hw hm
  exact complete_normal_injective hm hr hx hy

lemma fitChart_patch_bounds {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) (k : ℝ) :
    LipschitzOnWith 2 (fitChart s w m) (ribbonStepPatch k) ∧
      ∀ z ∈ ribbonStepPatch k, ∀ z' ∈ ribbonStepPatch k,
        dist z z' ≤ 2 * dist (fitChart s w m z) (fitChart s w m z') := by
  obtain ⟨hr, hx, hy, _⟩ := fit_parameters hs w hw hm
  exact complete_normal_patch_bounds m hr hx (by linarith [Nat.cast_nonneg (α := ℝ) m]) k

lemma fitChart_upper {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) :
    ∀ z ∈ closedRibbon, 0 < z.re → fitChart s w m z ∈ upperHalfPlane := by
  obtain ⟨hr, hx, hy, hH⟩ := fit_parameters hs w hw hm
  intro z hz hz0
  exact complete_normal_upper hm (by linarith) (by linarith) hx
    (by linarith [Nat.cast_nonneg (α := ℝ) m]) hz0 hz.2

lemma fitChart_initial {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) {z : ℂ} (hz : z.re ≤ fitHeight m) :
    fitChart s w m z = Complex.I * z := by
  obtain ⟨hr, hx, _, _⟩ := fit_parameters hs w hw hm
  have hA := fit_entry_lower hs w hw hm
  change normalRibbon (completeSpine m (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m))
    (completeTangent m (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)) z = _
  rw [complete_normal_of_le m _ _ _ _ (hz.trans hA)]
  obtain ⟨hσ, hT⟩ := lowConnector_initial (by linarith : 0 < fitRadius m) hx hz
  rw [normalRibbon, hσ, hT]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring

lemma fitChart_width (s : ℝ) (w : ℂ) (m : ℕ) {z : ℂ} (hz : z ∈ closedRibbon) :
    ‖fitChart s w m z - fitSpine s w m z.re‖ ≤ 1 :=
  complete_normal_width m _ _ _ _ hz.2

lemma fitSpine_eventually_ray (s : ℝ) (w : ℂ) (m : ℕ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      fitSpine s w m t = fitSpine s w m T + ((t - T : ℝ) : ℂ) * Complex.I :=
  complete_eventually_ray m _ _ _ _

lemma fit_scaled_arrayCenter {s : ℝ} (hs : 0 < s) (w : ℂ) {m : ℕ} (hm : 0 < m) :
    (ribbonWidth (halfHeight s) m : ℂ) * arrayCenter m (fitX s w m) (fitY s w m) =
      positiveCenter s w := by
  have hℓ := (fit_width_pos hs hm).ne'
  have hmul := fit_width_mul hs hm
  apply Complex.ext <;>
    simp only [arrayCenter, positiveCenter, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  · unfold fitX
    rw [mul_add, mul_div_cancel₀ _ hℓ]
    unfold halfHeight at *
    nlinarith
  · unfold fitY
    rw [mul_add, mul_div_cancel₀ _ hℓ]
    unfold halfHeight at *
    nlinarith

end SLEExactGauge.Serpentine

end

end OAI
