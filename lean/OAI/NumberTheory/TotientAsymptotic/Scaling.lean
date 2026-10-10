import OAI.NumberTheory.TotientAsymptotic.Normalization

namespace OAI

/-!
The common-endpoint argument from Proposition `mass` in the manuscript.
`CommonEndpointComparison` names an internal estimate still requiring proof;
it is not classified as a published input.  The proof below shows precisely
how that estimate and Ford's published order bounds yield regular variation,
without any phase-continuity assumption.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def pairedNormalized (c x : ℝ) : ℝ :=
  V (x/c) * Real.log x / ((x/c) * G x (m x))

def CommonEndpointComparison (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ H : ℕ, ∀ᶠ x : ℝ in atTop,
    |massError x H x| ≤ ε ∧ |massError x H (x/c)| ≤ ε

lemma paired_normalized_sub_tendsto {c : ℝ} (hcommon : CommonEndpointComparison c) :
    Tendsto (fun x => pairedNormalized c x - normalizedCount V x) atTop (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨H, hH⟩ := hcommon (ε/3) (by positivity)
  filter_upwards [hH] with x hx
  rw [Real.dist_eq, sub_zero]
  have heq : pairedNormalized c x - normalizedCount V x =
      massError x H (x/c) - massError x H x := by
    rw [normalizedCount_eq]
    unfold pairedNormalized massError
    ring
  rw [heq]
  calc
    |massError x H (x/c) - massError x H x| ≤
        |massError x H (x/c)| + |massError x H x| := abs_sub _ _
    _ ≤ ε/3 + ε/3 := add_le_add hx.2 hx.1
    _ < ε := by linarith

/-- The reciprocal form is convenient because Ford's lower bound controls
its denominator at the larger endpoint directly. -/
theorem inverse_scaling_of_internal_comparison {c : ℝ} (hc : 0 < c)
    (hford : FordScaleBounds) (hcommon : CommonEndpointComparison c) :
    Tendsto (fun x => V (x/c) / V x) atTop (nhds (1/c)) := by
  obtain ⟨a, b, ha, hbounds⟩ := hford
  have hdiff := paired_normalized_sub_tendsto hcommon
  have hsmall : Tendsto
      (fun x => (pairedNormalized c x - normalizedCount V x) / normalizedCount V x)
      atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun x =>
      |pairedNormalized c x - normalizedCount V x| / a)
    · filter_upwards [hbounds] with x hx
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (ha.trans_le hx.1)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) ha hx.1
    · simpa using hdiff.abs.div_const a
  have hlim : Tendsto (fun x =>
      ((pairedNormalized c x - normalizedCount V x) / normalizedCount V x + 1) / c)
      atTop (nhds (1/c)) := by
    simpa using (hsmall.add_const 1).div_const c
  apply hlim.congr'
  have hb : Tendsto B atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hbounds, eventually_gt_atTop (1 : ℝ),
    hb.eventually (eventually_gt_atTop 0)] with x hx hx1 hBx
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx1).ne'
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
  have hG : G x (m x) ≠ 0 := (G_pos hBx _).ne'
  have hV : V x ≠ 0 := by
    intro hzero
    have hpos := ha.trans_le hx.1
    simp [normalizedCount, hzero] at hpos
  rw [normalizedCount_eq]
  unfold pairedNormalized
  field_simp
  ring

/-- The endpoint comparison yields the manuscript's fixed-scale conclusion.
The unproved internal comparison remains explicit in this reduction theorem. -/
theorem scaling_of_internal_comparison {c : ℝ} (hc : 0 < c)
    (hford : FordScaleBounds) (hcommon : CommonEndpointComparison c) :
    Tendsto (fun x => V (c*x) / V x) atTop (nhds c) := by
  have ht := (inverse_scaling_of_internal_comparison hc hford hcommon).inv₀
    (one_div_ne_zero hc.ne')
  have hmul : Tendsto (fun x : ℝ => c*x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).2 tendsto_id
  have hh := ht.comp hmul
  simpa [Function.comp_def, inv_div, hc.ne'] using hh

end TotientAsymptotic
end

end OAI
