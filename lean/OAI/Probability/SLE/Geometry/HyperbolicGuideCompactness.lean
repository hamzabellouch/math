import Mathlib
import OAI.Probability.SLE.AngularLaws

namespace OAI

/-!
The hyperbolic confinement step in `es:guide-compactness`. A bound on the
actual velocity divided by height controls the logarithm of height. A single
normalized waypoint then gives compact containment and a common Euclidean
Lipschitz bound on each fixed interval away from the tip.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace SLEExactGauge.HyperbolicGuideCompactness

theorem log_height_lipschitz
    {β : ℝ → ℂ} {δ T K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ t ∈ Icc δ T, DifferentiableAt ℝ β t)
    (hH : ∀ t ∈ Icc δ T, 0 < (β t).im)
    (hv : ∀ t ∈ Icc δ T, ‖deriv β t‖ ≤ K * (β t).im) :
    LipschitzOnWith ⟨K, hK⟩ (fun t => Real.log (β t).im) (Icc δ T) := by
  have hd (t : ℝ) (ht : t ∈ Icc δ T) :
      HasDerivAt (fun u => Real.log (β u).im) ((deriv β t).im / (β t).im) t := by
    have hh := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hD t ht).hasDerivAt
    have hi : HasDerivAt (fun u => (β u).im) (deriv β t).im t := by
      simpa only [Function.comp_def, Complex.imCLM_apply] using hh
    exact hi.log (hH t ht).ne'
  apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Icc δ T)
    (fun t ht => (hd t ht).hasDerivWithinAt)
  intro t ht
  change ‖(deriv β t).im / (β t).im‖ ≤ K
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hH t ht)]
  exact (div_le_iff₀ (hH t ht)).mpr ((Complex.abs_im_le_norm _).trans (hv t ht))

lemma interval_dist_le_width {δ T s t : ℝ} (hs : s ∈ Icc δ T) (ht : t ∈ Icc δ T) :
    dist s t ≤ T - δ := by
  rw [Real.dist_eq]
  exact abs_le.mpr ⟨by linarith [hs.1, hs.2, ht.1, ht.2],
    by linarith [hs.1, hs.2, ht.1, ht.2]⟩

/-- Exponential upper and lower height bounds follow directly from the
log-height derivative estimate, without assuming a geometric confinement
result. -/
theorem height_bounds_from_waypoint
    {β : ℝ → ℂ} {δ T tw K s : ℝ} (hK : 0 ≤ K) (hs : 0 < s)
    (htw : tw ∈ Icc δ T)
    (hD : ∀ t ∈ Icc δ T, DifferentiableAt ℝ β t)
    (hH : ∀ t ∈ Icc δ T, 0 < (β t).im)
    (hv : ∀ t ∈ Icc δ T, ‖deriv β t‖ ≤ K * (β t).im)
    (hway : ‖β tw‖ = 1) (hangle : s ≤ (β tw).im) :
    ∀ t ∈ Icc δ T,
      s * Real.exp (-K * (T - δ)) ≤ (β t).im ∧
      (β t).im ≤ Real.exp (K * (T - δ)) := by
  have hL := log_height_lipschitz hK hD hH hv
  have hlogway : Real.log (β tw).im ≤ 0 :=
    Real.log_nonpos (hH tw htw).le ((Complex.im_le_norm _).trans_eq hway)
  have hlogs : Real.log s ≤ Real.log (β tw).im := Real.log_le_log hs hangle
  intro t ht
  have hdist := interval_dist_le_width ht htw
  have hh := hL.dist_le_mul t ht tw htw
  change dist (Real.log (β t).im) (Real.log (β tw).im) ≤ K * dist t tw at hh
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hdist hK)
  rw [Real.dist_eq] at hh'
  have hlo : Real.log s + (-K * (T - δ)) ≤ Real.log (β t).im := by
    have hab := (abs_le.mp hh').1
    nlinarith
  have hup : Real.log (β t).im ≤ K * (T - δ) := by
    have hab := (abs_le.mp hh').2
    linarith
  constructor
  · calc
      s * Real.exp (-K * (T - δ)) = Real.exp (Real.log s + (-K * (T - δ))) := by
        rw [Real.exp_add, Real.exp_log hs]
      _ ≤ Real.exp (Real.log (β t).im) := Real.exp_le_exp.mpr hlo
      _ = (β t).im := Real.exp_log (hH t ht)
  · simpa only [Real.exp_log (hH t ht)] using Real.exp_le_exp.mpr hup

def speedBound (K δ T : ℝ) : ℝ := K * Real.exp (K * (T - δ))

def radiusBound (K δ T : ℝ) : ℝ := 1 + speedBound K δ T * (T - δ)

theorem euclidean_lipschitz_from_waypoint
    {β : ℝ → ℂ} {δ T tw K s : ℝ} (hK : 0 ≤ K) (hs : 0 < s)
    (htw : tw ∈ Icc δ T)
    (hD : ∀ t ∈ Icc δ T, DifferentiableAt ℝ β t)
    (hH : ∀ t ∈ Icc δ T, 0 < (β t).im)
    (hv : ∀ t ∈ Icc δ T, ‖deriv β t‖ ≤ K * (β t).im)
    (hway : ‖β tw‖ = 1) (hangle : s ≤ (β tw).im) :
    LipschitzOnWith ⟨speedBound K δ T, mul_nonneg hK (Real.exp_pos _).le⟩
      β (Icc δ T) := by
  have hheight := height_bounds_from_waypoint hK hs htw hD hH hv hway hangle
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le hD _ (convex_Icc δ T)
  intro t ht
  change ‖deriv β t‖ ≤ speedBound K δ T
  exact (hv t ht).trans (mul_le_mul_of_nonneg_left (hheight t ht).2 hK)

theorem norm_bound_from_waypoint
    {β : ℝ → ℂ} {δ T tw K s : ℝ} (hK : 0 ≤ K) (hs : 0 < s)
    (htw : tw ∈ Icc δ T)
    (hD : ∀ t ∈ Icc δ T, DifferentiableAt ℝ β t)
    (hH : ∀ t ∈ Icc δ T, 0 < (β t).im)
    (hv : ∀ t ∈ Icc δ T, ‖deriv β t‖ ≤ K * (β t).im)
    (hway : ‖β tw‖ = 1) (hangle : s ≤ (β tw).im) :
    ∀ t ∈ Icc δ T, ‖β t‖ ≤ radiusBound K δ T := by
  have hL := euclidean_lipschitz_from_waypoint hK hs htw hD hH hv hway hangle
  intro t ht
  have hh := hL.dist_le_mul t ht tw htw
  have hsB : 0 ≤ speedBound K δ T := mul_nonneg hK (Real.exp_pos _).le
  have hdist := hh.trans (mul_le_mul_of_nonneg_left (interval_dist_le_width ht htw) hsB)
  rw [dist_eq_norm] at hdist
  change ‖β t - β tw‖ ≤ speedBound K δ T * (T - δ) at hdist
  have hn := norm_le_insert' (β t) (β tw)
  rw [hway] at hn
  exact hn.trans (by dsimp [radiusBound]; linarith)

/-- The common compact set obtained from the actual derivative estimates. -/
def confinementSet (K s δ T : ℝ) : Set ℂ :=
  closedBall 0 (radiusBound K δ T) ∩ {z | s * Real.exp (-K * (T - δ)) ≤ z.im}

theorem confinementSet_compact (K s δ T : ℝ) : IsCompact (confinementSet K s δ T) :=
  (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im)

theorem confinementSet_subset_halfPlane {K s δ T : ℝ} (hs : 0 < s) :
    confinementSet K s δ T ⊆ {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (mul_pos hs (Real.exp_pos _)).trans_le hz.2

/-- A normalized family with a common hyperbolic-speed bound is uniformly
equicontinuous and remains in one compact subset of the upper half-plane. -/
theorem family_compact_containment_equicontinuity
    (β : ℕ → ℝ → ℂ) {δ T tw K s : ℝ} (hK : 0 ≤ K) (hs : 0 < s)
    (htw : tw ∈ Icc δ T)
    (hD : ∀ n t, t ∈ Icc δ T → DifferentiableAt ℝ (β n) t)
    (hH : ∀ n t, t ∈ Icc δ T → 0 < (β n t).im)
    (hv : ∀ n t, t ∈ Icc δ T → ‖deriv (β n) t‖ ≤ K * (β n t).im)
    (hway : ∀ n, ‖β n tw‖ = 1) (hangle : ∀ n, s ≤ (β n tw).im) :
    IsCompact (confinementSet K s δ T) ∧
    confinementSet K s δ T ⊆ {z : ℂ | 0 < z.im} ∧
    (∀ n, MapsTo (β n) (Icc δ T) (confinementSet K s δ T)) ∧
    UniformEquicontinuousOn β (Icc δ T) := by
  have hL (n : ℕ) := euclidean_lipschitz_from_waypoint hK hs htw
    (hD n) (hH n) (hv n) (hway n) (hangle n)
  refine ⟨confinementSet_compact K s δ T, confinementSet_subset_halfPlane hs, ?_,
    LipschitzOnWith.uniformEquicontinuousOn β _ hL⟩
  intro n t ht
  refine ⟨?_, (height_bounds_from_waypoint hK hs htw
    (hD n) (hH n) (hv n) (hway n) (hangle n) t ht).1⟩
  simpa only [mem_closedBall, dist_zero_right] using
    norm_bound_from_waypoint hK hs htw (hD n) (hH n) (hv n) (hway n) (hangle n) t ht

/-- A univalent inverse chart on a physical clearance ball has derivative
bounded by its height. The omitted point is the real part of its center value. -/
theorem inverse_chart_derivative_bound
    {g : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ g (ball z r)) (hi : InjOn g (ball z r))
    (hH : MapsTo g (ball z r) {w : ℂ | 0 < w.im}) :
    ‖deriv g z‖ ≤ ((128 * Real.pi) / r) * (g z).im := by
  have hzH : 0 < (g z).im := hH (mem_ball_self hr)
  have hnot : ((g z).re : ℂ) ∉ g '' ball z r := by
    rintro ⟨w, hw, he⟩
    have hh : 0 < (g w).im := hH hw
    rw [he] at hh
    simp only [Complex.ofReal_im, lt_self_iff_false] at hh
  have hh := univalent_omitted_value_bound_ball hr hd hi ((g z).re : ℂ) hnot
  have hvalue : g z - ((g z).re : ℂ) = ((g z).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hn : ‖g z - ((g z).re : ℂ)‖ = (g z).im := by
    rw [hvalue, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzH,
      Complex.norm_I, mul_one]
  rw [hn] at hh
  calc
    ‖deriv g z‖ ≤ ((128 * Real.pi) * (g z).im) / r :=
      (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by ring

/-- Actual composition with a physical guide converts clearance and bounded
physical speed into the hyperbolic-speed estimate used above. -/
theorem inverse_guide_composition_bound
    {g : ℂ → ℂ} {α : ℝ → ℂ} {t r V : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball (α t) r)) (hgi : InjOn g (ball (α t) r))
    (hgH : MapsTo g (ball (α t) r) {w : ℂ | 0 < w.im})
    (hα : DifferentiableAt ℝ α t) (hv : ‖deriv α t‖ ≤ V) :
    DifferentiableAt ℝ (g ∘ α) t ∧
      ‖deriv (g ∘ α) t‖ ≤ ((128 * Real.pi * V) / r) * (g (α t)).im := by
  have hgd : DifferentiableAt ℂ g (α t) :=
    hg.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hcomp := (hgd.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hα.hasDerivAt
  refine ⟨hcomp.differentiableAt, ?_⟩
  have hval : (fderiv ℝ g (α t)) (deriv α t) = deriv α t * deriv g (α t) := by
    rw [hgd.fderiv_restrictScalars (𝕜 := ℝ)]
    change (fderiv ℂ g (α t)) (deriv α t) = _
    rw [fderiv_eq_smul_deriv, smul_eq_mul]
  have hnorm : ‖deriv (g ∘ α) t‖ = ‖deriv g (α t)‖ * ‖deriv α t‖ := by
    rw [hcomp.deriv, hval, norm_mul, mul_comm]
  have hh := inverse_chart_derivative_bound hr hg hgi hgH
  have hheight : 0 < (g (α t)).im := hgH (mem_ball_self hr)
  rw [hnorm]
  calc
    ‖deriv g (α t)‖ * ‖deriv α t‖ ≤
        (((128 * Real.pi) / r) * (g (α t)).im) * V :=
      mul_le_mul hh hv (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The family compactness conclusion with its hyperbolic-speed hypothesis
fully discharged by actual inverse charts and physical clearance balls. -/
theorem inverse_guide_family_compactness
    (g : ℕ → ℂ → ℂ) (α : ℕ → ℝ → ℂ) {δ T tw r V s : ℝ}
    (hr : 0 < r) (hV : 0 ≤ V) (hs : 0 < s) (htw : tw ∈ Icc δ T)
    (hg : ∀ n t, t ∈ Icc δ T → DifferentiableOn ℂ (g n) (ball (α n t) r))
    (hgi : ∀ n t, t ∈ Icc δ T → InjOn (g n) (ball (α n t) r))
    (hgH : ∀ n t, t ∈ Icc δ T → MapsTo (g n) (ball (α n t) r) {w : ℂ | 0 < w.im})
    (hα : ∀ n t, t ∈ Icc δ T → DifferentiableAt ℝ (α n) t)
    (hv : ∀ n t, t ∈ Icc δ T → ‖deriv (α n) t‖ ≤ V)
    (hway : ∀ n, ‖g n (α n tw)‖ = 1)
    (hangle : ∀ n, s ≤ (g n (α n tw)).im) :
    ∃ Q : Set ℂ, IsCompact Q ∧ Q ⊆ {z : ℂ | 0 < z.im} ∧
      (∀ n, MapsTo (g n ∘ α n) (Icc δ T) Q) ∧
      UniformEquicontinuousOn (fun n => g n ∘ α n) (Icc δ T) := by
  let K := (128 * Real.pi * V) / r
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcomp n t (ht : t ∈ Icc δ T) :=
    inverse_guide_composition_bound hr (hg n t ht) (hgi n t ht) (hgH n t ht)
      (hα n t ht) (hv n t ht)
  have hheight n t (ht : t ∈ Icc δ T) : 0 < ((g n ∘ α n) t).im :=
    hgH n t ht (mem_ball_self hr)
  exact ⟨confinementSet K s δ T,
    family_compact_containment_equicontinuity (fun n => g n ∘ α n) hK hs htw
      (fun n t ht => (hcomp n t ht).1) hheight (fun n t ht => (hcomp n t ht).2) hway hangle⟩

end SLEExactGauge.HyperbolicGuideCompactness

end

end OAI
