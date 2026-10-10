import OAI.NumberTheory.CubicMoment.Estimates.MellinSmooth

namespace OAI

/-! A compact logarithmic Schwartz profile gives an actual smooth norm
weight supported away from zero, with no loss in its logarithmic seminorms. -/
noncomputable section
open Set Filter
open scoped ContDiff SchwartzMap Topology
namespace CubicFirstMoment

def logSchwartzWeight (H : 𝓢(ℝ,ℂ)) (x : ℝ) : ℂ :=
  if 0 < x then H (-Real.log x) else 0

lemma logSchwartzWeight_exp (H : 𝓢(ℝ,ℂ)) (u : ℝ) :
    logSchwartzWeight H (Real.exp (-u))=H u := by
  simp only [logSchwartzWeight,Real.exp_pos,ite_true,Real.log_exp,neg_neg]

lemma logSchwartzWeight_zero_small (H : 𝓢(ℝ,ℂ)) {R : ℝ}
    (hR : ∀ u ∈ tsupport (H : ℝ → ℂ), |u| ≤ R)
    {x : ℝ} (hx : x < Real.exp (-R)) : logSchwartzWeight H x=0 := by
  by_cases hxp : 0 < x
  · rw [logSchwartzWeight,ite_eq_left hxp]
    by_contra hn
    have hh := hR (-Real.log x) (subset_tsupport _ hn)
    have hl := (Real.log_lt_iff_lt_exp hxp).mpr hx
    linarith [le_abs_self (-Real.log x)]
  · simp only [logSchwartzWeight,ite_eq_right hxp]

lemma logSchwartzWeight_zero_large (H : 𝓢(ℝ,ℂ)) {R : ℝ}
    (hR : ∀ u ∈ tsupport (H : ℝ → ℂ), |u| ≤ R)
    {x : ℝ} (hx : Real.exp R < x) : logSchwartzWeight H x=0 := by
  have hxp : 0 < x := (Real.exp_pos R).trans hx
  rw [logSchwartzWeight,ite_eq_left hxp]
  by_contra hn
  have hh := hR (-Real.log x) (subset_tsupport _ hn)
  have hl := (Real.lt_log_iff_exp_lt hxp).mpr hx
  linarith [neg_abs_le (-Real.log x)]

lemma logSchwartzWeight_support (H : 𝓢(ℝ,ℂ)) {R : ℝ}
    (hR : ∀ u ∈ tsupport (H : ℝ → ℂ), |u| ≤ R) :
    Function.support (logSchwartzWeight H) ⊆ Icc (Real.exp (-R)) (Real.exp R) := by
  intro x hx
  constructor
  · by_contra h
    exact hx (logSchwartzWeight_zero_small H hR (lt_of_not_ge h))
  · by_contra h
    exact hx (logSchwartzWeight_zero_large H hR (lt_of_not_ge h))

lemma logSchwartzWeight_compact (H : 𝓢(ℝ,ℂ)) {R : ℝ}
    (hR : ∀ u ∈ tsupport (H : ℝ → ℂ), |u| ≤ R) :
    HasCompactSupport (logSchwartzWeight H) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (logSchwartzWeight_support H hR)

lemma logSchwartzWeight_positive_support (H : 𝓢(ℝ,ℂ)) {R : ℝ}
    (hR : ∀ u ∈ tsupport (H : ℝ → ℂ), |u| ≤ R) :
    tsupport (logSchwartzWeight H) ⊆ Ioi 0 := by
  have hc := closure_minimal (logSchwartzWeight_support H hR) isClosed_Icc
  intro x hx
  exact (Real.exp_pos (-R)).trans_le (hc hx).1

lemma logSchwartzWeight_smooth (H : 𝓢(ℝ,ℂ)) {R : ℝ}
    (hR : ∀ u ∈ tsupport (H : ℝ → ℂ), |u| ≤ R) :
    ContDiff ℝ ∞ (logSchwartzWeight H) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · have he : logSchwartzWeight H =ᶠ[𝓝 x] fun y => H (-Real.log y) := by
      filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds hx] with y hy
      exact ite_eq_left hy
    have hl : ContDiffAt ℝ ∞ (fun y : ℝ => -Real.log y) x :=
      (contDiffAt_id.log hx.ne').neg
    exact ((H.smooth ⊤).contDiffAt.comp x hl).congr_of_eventuallyEq he
  · have hxe : x < Real.exp (-R) := (le_of_not_gt hx).trans_lt (Real.exp_pos _)
    have he : logSchwartzWeight H =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_id continuous_const).mem_nhds hxe] with y hy
      exact logSchwartzWeight_zero_small H hR hy
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma logSchwartzWeight_log_profile (H : 𝓢(ℝ,ℂ)) {R : ℝ}
    (hR : ∀ u ∈ tsupport (H : ℝ → ℂ), |u| ≤ R) :
    mellinLogSchwartz (logSchwartzWeight H) (logSchwartzWeight_compact H hR)
      (logSchwartzWeight_positive_support H hR) (logSchwartzWeight_smooth H hR) 0=H := by
  ext u
  simp only [mellinLogSchwartz_apply,neg_zero,zero_mul,Real.exp_zero,one_smul,
    logSchwartzWeight_exp]

end CubicFirstMoment

end

end OAI
