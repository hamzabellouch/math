import OAI.Probability.SLE.Gauge.RibbonCoordinateGeometry
import OAI.Probability.SLE.Loewner.ActualRadiusStops

namespace OAI

/-! The dense experiment need not classify the filled hull of its obstacle.
A free upward corridor puts the marked-point ball in the actual unbounded
surviving component and gives its conformal-radius cutoff directly. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

/-- The upward shadow of a ball, with a slightly larger rectangular base. -/
def upwardShadow (w : ℂ) (r : ℝ) : Set ℂ :=
  {z | |z.re - w.re| < r ∧ w.im - r < z.im}

lemma upwardRay_mem_shadow {w z : ℂ} {r : ℝ} (hz : z ∈ ball w r) (t : ℝ≥0) :
    upwardRay z t ∈ upwardShadow w r := by
  have hd : ‖z - w‖ < r := by simpa only [mem_ball, dist_eq_norm] using hz
  have hre : |z.re - w.re| < r :=
    (Complex.abs_re_le_norm (z - w)).trans_lt hd
  have him : |z.im - w.im| < r :=
    (Complex.abs_im_le_norm (z - w)).trans_lt hd
  have hlow := (abs_lt.mp him).1
  simp only [upwardRay, upwardShadow, mem_ofPred_eq, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  exact ⟨hre, by linarith [t.coe_nonneg]⟩

lemma marked_ball_survives_of_free_upwardShadow
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0) (w : ℂ) {r : ℝ} (_hr : 0 < r)
    (hheight : r ≤ w.im)
    (hfree : Disjoint (γ '' Icc 0 T) (upwardShadow w r)) :
    ball w r ⊆ survivingDomain γ T := by
  intro z hz
  have hshadow := upwardRay_mem_shadow hz
  have hroute : range (upwardRay z) ⊆ upperHalfPlane \ (γ '' Icc 0 T) := by
    rintro u ⟨t, rfl⟩
    refine ⟨?_, ?_⟩
    · have hh := (hshadow t).2
      change 0 < (upwardRay z t).im
      linarith
    · intro hpast
      exact disjoint_left.mp hfree hpast (hshadow t)
  have hsurv := survives_of_unbounded_free_curve γ T (upwardRay z)
    (upwardRay_continuous z) hroute (upwardRay_unbounded z) (mem_range_self 0)
  simpa only [upwardRay, NNReal.coe_zero, Complex.ofReal_zero, zero_mul, add_zero] using hsurv

lemma fullRadius_lower_of_surviving_ball
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (w : ℂ) {r : ℝ} (hr : 0 < r)
    (hball : ball w r ⊆ survivingDomain γ T) : r ≤ fullRadius G T w := by
  have hlive := hball (mem_ball_self hr)
  apply radius_of_halfplane_map hr ((hw.2.2.2.1 T).mono hball)
    (fun z hz => hw.2.2.2.2.2.1 T (hball hz))
  exact norm_ne_zero_iff.mp (hw.derivative_norm_positive hU T w hlive).ne'

/-- Uniform free clearance gives the actual radius bound throughout every
successful prefix. Filled-hull containment is unnecessary. -/
theorem experiment_radius_lower_from_shadow
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (w : ℂ) {r : ℝ} (hr : 0 < r) (hheight : r ≤ w.im)
    (hfree : Disjoint (γ '' Icc 0 T) (upwardShadow w r)) :
    ∀ t : ℝ≥0, t ≤ T → w ∈ survivingDomain γ t ∧ r ≤ fullRadius G t w := by
  intro t ht
  have hball := marked_ball_survives_of_free_upwardShadow γ T w hr hheight hfree
  have hballt : ball w r ⊆ survivingDomain γ t :=
    hball.trans (survivingDomain_antitone γ ht)
  exact ⟨hballt (mem_ball_self hr), fullRadius_lower_of_surviving_ball hU hw t w hr hballt⟩

lemma completion_before_radiusLevelTime_of_prefix_lower
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (w : ℂ) (u r : ℝ)
    (hprefix : ∀ t : ℝ≥0, t ≤ T → w ∈ survivingDomain γ t ∧ r ≤ fullRadius G t w)
    (hcutoff : (2 * w.im) * Real.exp (-u) < r) :
    (T : ℝ≥0∞) < radiusLevelTime γ G w u := by
  by_contra hn
  have hle := le_of_not_gt hn
  have hfinite : radiusLevelTime γ G w u < ∞ := hle.trans_lt ENNReal.coe_lt_top
  obtain ⟨t, ht, hR⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G w u hfinite
  rw [radiusLevelTime_eq_of_live_level hU hw w u t ht hR] at hle
  have htT : t ≤ T := by exact_mod_cast hle
  have hb := (hprefix t htT).2
  rw [hR] at hb
  exact (not_le_of_gt hcutoff) hb

end SLEExactGauge

end

end OAI
