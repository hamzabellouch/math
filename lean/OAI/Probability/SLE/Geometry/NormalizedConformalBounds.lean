import OAI.Probability.SLE.Geometry.PublishedConformalCompactness
import OAI.Probability.SLE.Gauge.ConformalCompactSausage

namespace OAI

/-! Interior derivative bounds for the normalized inverse maps used to
transport the dense experiment. The only input is the existing published
compactness consequence for the schlicht class. -/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace SLEExactGauge

def normalizedInteriorCompact (s : ℝ) : Set ℂ :=
  {z | ‖z‖ ≤ 2 ∧ s / 2 ≤ z.im}

lemma normalizedInteriorCompact_isCompact (s : ℝ) :
    IsCompact (normalizedInteriorCompact s) := by
  have he : normalizedInteriorCompact s =
      closedBall (0 : ℂ) 2 ∩ {z : ℂ | s / 2 ≤ z.im} := by
    ext z
    simp only [normalizedInteriorCompact, mem_ofPred_eq, mem_inter_iff,
      mem_closedBall, dist_zero_right]
  rw [he]
  exact (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const Complex.continuous_im)

lemma normalizedInteriorCompact_nonempty {s : ℝ} (hs : s ≤ 1) :
    (normalizedInteriorCompact s).Nonempty := by
  refine ⟨Complex.I, ?_⟩
  change ‖Complex.I‖ ≤ 2 ∧ s / 2 ≤ Complex.I.im
  simp only [Complex.norm_I, Complex.I_im]
  constructor <;> linarith

lemma normalizedInteriorCompact_subset_halfPlane {s : ℝ} (hs : 0 < s) :
    normalizedInteriorCompact s ⊆ upperHalfPlane := by
  intro z hz
  change 0 < z.im
  exact (half_pos hs).trans_le hz.2

/-- The interior normalization fixes the value and the derivative norm
at a unit semicircle waypoint. -/
structure IsNormalizedHalfPlaneMap (s : ℝ) (F : ℂ → ℂ) (w : ℂ) : Prop where
  differentiable : DifferentiableOn ℂ F upperHalfPlane
  injective : InjOn F upperHalfPlane
  waypoint_norm : ‖w‖ = 1
  waypoint_height : s ≤ w.im
  value : F w = 0
  derivative_norm : ‖deriv F w‖ = 1

theorem uniform_normalized_derivative_bounds
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (F : ℂ → ℂ) (w : ℂ), IsNormalizedHalfPlaneMap s F w →
        ∀ z ∈ normalizedInteriorCompact s,
          c ≤ ‖deriv F z‖ ∧ ‖deriv F z‖ ≤ C := by
  classical
  by_contra hnone
  push Not at hnone
  have hfail (n : ℕ) : ∃ (F : ℂ → ℂ) (w : ℂ),
      IsNormalizedHalfPlaneMap s F w ∧
      ∃ z ∈ normalizedInteriorCompact s,
        ‖deriv F z‖ < 1 / ((n : ℝ) + 1) ∨ (n : ℝ) + 1 < ‖deriv F z‖ := by
    obtain ⟨F, w, hF, z, hz, hbad⟩ :=
      hnone (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) (by positivity) (by positivity)
    refine ⟨F, w, hF, z, hz, ?_⟩
    by_cases hlo : ‖deriv F z‖ < 1 / ((n : ℝ) + 1)
    · exact Or.inl hlo
    · exact Or.inr (hbad (le_of_not_gt hlo))
  choose F w hF z hz hbad using hfail
  obtain ⟨φ, G, hφ, hG, _hi, hne, hconv⟩ := hcompact F w s 1 1 hs zero_lt_one
    (fun n => (hF n).differentiable) (fun n => (hF n).injective)
    (fun n => ⟨(hF n).waypoint_norm, (hF n).waypoint_height⟩)
    (fun n => by rw [(hF n).value]; simp)
    (fun n => by rw [(hF n).derivative_norm]; exact ⟨le_rfl, le_rfl⟩)
  obtain ⟨c, C, hc, _hC, hb⟩ := eventually_derivative_norm_bounds_on_compact
    (fun n => F (φ n)) G (fun n => (hF (φ n)).differentiable) hG hconv
    (normalizedInteriorCompact s) (normalizedInteriorCompact_isCompact s)
    (normalizedInteriorCompact_nonempty hs1) (normalizedInteriorCompact_subset_halfPlane hs)
    (fun z hz => hne z (normalizedInteriorCompact_subset_halfPlane hs hz))
  have hsmall : ∀ᶠ n in atTop, 1 / ((φ n : ℝ) + 1) < c :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).eventually (gt_mem_nhds hc)
  have hlarge : ∀ᶠ n in atTop, C < (φ n : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop).eventually_gt_atTop C
  obtain ⟨n, hbn, hsn, hln⟩ := (hb.and (hsmall.and hlarge)).exists
  have hbounds := hbn (z (φ n)) (hz (φ n))
  rcases hbad (φ n) with hlo | hhi
  · exact (not_lt_of_ge hbounds.1) (hlo.trans hsn)
  · exact (not_lt_of_ge hbounds.2) (lt_trans (by linarith) hhi)

/-- The same bounds with the normalization hypotheses exposed individually. -/
theorem uniform_normalized_derivative_bounds_explicit
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (F : ℂ → ℂ) (w : ℂ), DifferentiableOn ℂ F upperHalfPlane →
        InjOn F upperHalfPlane → ‖w‖ = 1 → s ≤ w.im → F w = 0 →
        ‖deriv F w‖ = 1 → ∀ z : ℂ, ‖z‖ ≤ 2 → s / 2 ≤ z.im →
          c ≤ ‖deriv F z‖ ∧ ‖deriv F z‖ ≤ C := by
  obtain ⟨c, C, hc, hC, hbound⟩ := uniform_normalized_derivative_bounds hcompact hs hs1
  refine ⟨c, C, hc, hC, ?_⟩
  intro F w hd hi hwn hwh hw0 hwd z hzn hzh
  exact hbound F w ⟨hd, hi, hwn, hwh, hw0, hwd⟩ z ⟨hzn, hzh⟩

/-- Centering and dividing by the waypoint derivative gives the relative
bounds used for an arbitrary inverse chart. -/
theorem uniform_waypoint_derivative_ratios
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (F : ℂ → ℂ) (w : ℂ), DifferentiableOn ℂ F upperHalfPlane →
        InjOn F upperHalfPlane → ‖w‖ = 1 → s ≤ w.im → deriv F w ≠ 0 →
        ∀ z : ℂ, ‖z‖ ≤ 2 → s / 2 ≤ z.im →
          c * ‖deriv F w‖ ≤ ‖deriv F z‖ ∧ ‖deriv F z‖ ≤ C * ‖deriv F w‖ := by
  obtain ⟨c, C, hc, hC, hbound⟩ := uniform_normalized_derivative_bounds hcompact hs hs1
  refine ⟨c, C, hc, hC, ?_⟩
  intro F w hd hi hwn hwh hne z hzn hzh
  have hscale : 0 < ‖deriv F w‖ := norm_pos_iff.mpr hne
  have hden : (‖deriv F w‖ : ℂ) ≠ 0 := by exact_mod_cast hscale.ne'
  let A : ℂ → ℂ := fun u => (F u - F w) / (‖deriv F w‖ : ℂ)
  have hAder (u : ℂ) : deriv A u = deriv F u / (‖deriv F w‖ : ℂ) := by
    simp only [A, deriv_div_const, deriv_sub_const]
  have hAn : IsNormalizedHalfPlaneMap s A w := by
    refine ⟨(hd.sub_const _).div_const _, ?_, hwn, hwh, ?_, ?_⟩
    · intro u hu v hv he
      apply hi hu hv
      have he' : F u - F w = F v - F w := (div_left_inj' hden).mp he
      exact sub_left_injective he'
    · simp only [A, sub_self, zero_div]
    · rw [hAder, norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self hscale.ne']
  have hh := hbound A w hAn z ⟨hzn, hzh⟩
  rw [hAder, norm_div, Complex.norm_of_nonneg (norm_nonneg _)] at hh
  exact ⟨(le_div_iff₀ hscale).mp hh.1, (div_le_iff₀ hscale).mp hh.2⟩

end SLEExactGauge

end

end OAI
