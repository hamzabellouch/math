import Mathlib
import OAI.Analysis.Crouzeix.PoissonExtension

namespace OAI

/-! Harmonic Maximum. -/

noncomputable section

open Set Filter Metric Topology Function Complex InnerProductSpace Real

namespace CrouzeixHilbert.Conformal

theorem harmonic_eventually_eq_of_isLocalMax {u : ℂ → ℝ} {p : ℂ}
    (hu : HarmonicAt u p) (hm : IsLocalMax u p) :
    u =ᶠ[𝓝 p] (fun _ => u p) := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hu.eventually
  obtain ⟨f, hf, he⟩ := HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
    (show HarmonicOnNhd u (ball p r) from hsub)
  have hp : p ∈ ball p r := mem_ball_self hr
  have hfd : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (fun w => Complex.exp (f w)) z := by
    filter_upwards [ball_mem_nhds p hr] with z hz
    exact (Complex.differentiable_exp.differentiableAt.comp z (hf z hz).differentiableAt)
  have hfm : IsLocalMax (norm ∘ (fun w => Complex.exp (f w))) p := by
    filter_upwards [hm, ball_mem_nhds p hr] with z hz hzB
    simp only [Function.comp_apply, Complex.norm_exp, he hzB, he hp]
    exact Real.exp_le_exp.mpr hz
  have hc := Complex.norm_eventually_eq_of_isLocalMax hfd hfm
  filter_upwards [hc, ball_mem_nhds p hr] with z hz hzB
  have := hz
  simp only [Complex.norm_exp, he hzB, he hp, Real.exp_eq_exp] at this
  exact this

theorem harmonic_eqOn_of_isLocalMax {U : Set ℂ} (hU : IsPreconnected U)
    {u : ℂ → ℝ} (hu : HarmonicOnNhd u U) {p : ℂ} (hp : p ∈ U)
    (hm : IsLocalMax u p) : EqOn u (fun _ => u p) U :=
  (show AnalyticOnNhd ℝ u U from fun z hz => _root_.HarmonicAt.analyticAt (hu z hz))
    |>.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hU hp
      (harmonic_eventually_eq_of_isLocalMax (hu p hp) hm)

theorem harmonic_le_of_boundary_le {U : Set ℂ} (hU : IsOpen U)
    (hc : IsPreconnected U) (hb : Bornology.IsBounded U) {u : ℂ → ℝ}
    (hu : HarmonicContOnCl u U) {C : ℝ} (hbd : ∀ z ∈ frontier U, u z ≤ C) :
    ∀ z ∈ closure U, u z ≤ C := by
  intro z hz
  obtain ⟨p, hp, hmax⟩ := hb.isCompact_closure.exists_isMaxOn ⟨z, hz⟩ hu.continuousOn
  suffices u p ≤ C from (hmax hz).trans this
  by_cases hpi : p ∈ U
  · have he := (harmonic_eqOn_of_isLocalMax hc hu.harmonicOnNhd hpi
      (hmax.isLocalMax (mem_of_superset (hU.mem_nhds hpi) subset_closure))).of_subset_closure
        hu.continuousOn continuousOn_const subset_closure Subset.rfl
    obtain ⟨q, hq⟩ := nonempty_frontier_iff.mpr ⟨⟨p, hpi⟩, (fun he => NormedSpace.unbounded_univ ℂ ℂ (he ▸ hb))⟩
    simpa only [he (frontier_subset_closure hq)] using hbd q hq
  · exact hbd p ⟨hp, by simpa only [hU.interior_eq] using hpi⟩

theorem harmonic_eqOn_of_boundary_eq {U : Set ℂ} (hU : IsOpen U)
    (hc : IsPreconnected U) (hb : Bornology.IsBounded U) {u v : ℂ → ℝ}
    (hu : HarmonicContOnCl u U) (hv : HarmonicContOnCl v U)
    (he : EqOn u v (frontier U)) : EqOn u v (closure U) := by
  have hle := harmonic_le_of_boundary_le hU hc hb (hu.sub hv)
    (C := 0) (fun z hz => by change u z - v z ≤ 0; rw [he hz, sub_self])
  have hge := harmonic_le_of_boundary_le hU hc hb (hv.sub hu)
    (C := 0) (fun z hz => by change v z - u z ≤ 0; rw [he hz, sub_self])
  intro z hz
  exact le_antisymm (sub_nonpos.mp (hle z hz)) (sub_nonpos.mp (hge z hz))

end CrouzeixHilbert.Conformal

end

end OAI
