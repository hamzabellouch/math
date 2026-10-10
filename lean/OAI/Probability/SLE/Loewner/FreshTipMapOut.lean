import OAI.Probability.SLE.PhysicalTransport
import OAI.Probability.SLE.Gauge.RibbonSurvival

namespace OAI

/-! Mapping the actual geometric continuation into the restarted half-plane.
At a first height crossing the tip is fresh. The fresh-tip chart limit then maps a simple access path continuously to a simple path
starting at the restarted driving point. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal unitInterval

namespace SLEExactGauge

theorem tip_survives_prior_of_strict_height
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0) (hheight : 0 < (γ T).im)
    (hfirst : ∀ u : ℝ≥0, u < T → (γ u).im < (γ T).im) :
    ∀ s : ℝ≥0, s < T → γ T ∈ survivingDomain γ s := by
  intro s hs
  have hfree : range (upwardRay (γ T)) ⊆ upperHalfPlane \ (γ '' Icc 0 s) := by
    rintro z ⟨u, rfl⟩
    have him : (upwardRay (γ T) u).im = (γ T).im + (u : ℝ) := by simp [upwardRay]
    refine ⟨by change 0 < (upwardRay (γ T) u).im; rw [him]; positivity, ?_⟩
    rintro ⟨v, hv, he⟩
    have hh := hfirst v (hv.2.trans_lt hs)
    have he' := congrArg Complex.im he
    rw [him] at he'
    linarith [u.coe_nonneg]
  have hh := survives_of_unbounded_free_curve γ s (upwardRay (γ T))
    (upwardRay_continuous _) hfree (upwardRay_unbounded _) (mem_range_self 0)
  simpa only [upwardRay, NNReal.coe_zero, Complex.ofReal_zero, zero_mul, add_zero] using hh

/-- Extend the map only at the accessible tip. This is sufficient to map
the entire simple continuation Path, and does not require a boundary
extension of the forward conformal map at other hull points. -/
theorem map_out_simple_access_path
    (D : Set ℂ) (_hD : IsOpen D) (g : ℂ → ℂ)
    (hg : ContinuousOn g D) (hgi : InjOn g D) (hgH : MapsTo g D upperHalfPlane)
    (ζ w : ℂ) (u : ℝ) (hζ : ζ ∉ D)
    (hlim : Tendsto g (𝓝[D] ζ) (𝓝 (u : ℂ)))
    (p : Path ζ w) (hp : Function.Injective p)
    (hpD : ∀ t, t ≠ 0 → p t ∈ D) :
    ∃ q : Path (0 : ℂ) (g w - (u : ℂ)), Function.Injective q ∧
      (∀ t, t ≠ 0 → q t ∈ upperHalfPlane) ∧
      (∀ t, t ≠ 0 → q t = g (p t) - (u : ℂ)) := by
  classical
  let gb := Function.update g ζ (u : ℂ)
  have hs : insert ζ D \ {ζ} = D := by
    ext z
    simp only [Set.mem_sdiff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨rfl | hz, hn⟩
      · exact False.elim (hn rfl)
      · exact hz
    · intro hz
      exact ⟨Or.inr hz, fun he => hζ (he ▸ hz)⟩
  have hgb : ContinuousOn gb (insert ζ D) := by
    rw [continuousOn_update_iff, hs]
    exact ⟨hg, fun _ => hlim⟩
  have hpS : range p ⊆ insert ζ D := by
    rintro z ⟨t, rfl⟩
    by_cases ht : t = 0
    · simpa only [ht, p.source] using mem_insert ζ D
    · exact mem_insert_of_mem ζ (hpD t ht)
  have hne (t : unitInterval) (ht : t ≠ 0) : p t ≠ ζ :=
    fun he => hζ (he ▸ hpD t ht)
  have heval (t : unitInterval) (ht : t ≠ 0) : gb (p t) = g (p t) :=
    Function.update_of_ne (hne t ht) _ _
  have hw : gb w = g w := by
    simpa only [p.target] using heval 1 one_ne_zero
  let q : Path (0 : ℂ) (g w - (u : ℂ)) := {
    toFun := fun t => gb (p t) - (u : ℂ)
    continuous_toFun := ((hgb.mono hpS).comp_continuous p.continuous
      (fun t => mem_range_self t)).sub continuous_const
    source' := by simp [gb]
    target' := by simp only [p.target, hw] }
  have hqH (t : unitInterval) (ht : t ≠ 0) : q t ∈ upperHalfPlane := by
    change 0 < (gb (p t) - (u : ℂ)).im
    rw [heval t ht]
    simpa only [upperHalfPlane, mem_ofPred_eq, Complex.sub_im, Complex.ofReal_im,
      sub_zero] using hgH (hpD t ht)
  refine ⟨q, ?_, hqH, fun t ht => by change gb (p t) - _ = _; rw [heval t ht]⟩
  intro s t he
  by_cases hs0 : s = 0
  · subst s
    by_contra ht0
    have hh := hqH t (Ne.symm ht0)
    rw [← he, q.source] at hh
    simp only [upperHalfPlane, mem_ofPred_eq, Complex.zero_im, lt_self_iff_false] at hh
  by_cases ht0 : t = 0
  · subst t
    have hh := hqH s hs0
    rw [he, q.source] at hh
    simp only [upperHalfPlane, mem_ofPred_eq, Complex.zero_im, lt_self_iff_false] at hh
  apply hp
  apply hgi (hpD s hs0) (hpD t ht0)
  have he' : gb (p s) - (u : ℂ) = gb (p t) - (u : ℂ) := he
  rw [heval s hs0, heval t ht0] at he'
  exact sub_left_injective he'

/-- Actual capacity charts at a first height crossing map the physical
simple continuation to a supported simple path in the restarted half-plane,
with the conformal map-back identity at every positive path time. -/
theorem IsCapacityTwoWitness.map_out_access_at_first_height
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (T : ℝ≥0) (hT : 0 < T) (hheight : 0 < (γ T).im)
    (hfirst : ∀ u : ℝ≥0, u < T → (γ u).im < (γ T).im)
    (w : ℂ) (p : Path (γ T) w) (hp : Function.Injective p)
    (hpD : ∀ t, t ≠ 0 → p t ∈ survivingDomain γ T) :
    ∃ q : Path (0 : ℂ) (G T w - (U T : ℂ)), Function.Injective q ∧
      (∀ t, t ≠ 0 → q t ∈ upperHalfPlane) ∧
      (∀ t, t ≠ 0 → F T (q t + (U T : ℂ)) = p t) := by
  have hgi : InjOn (G T) (survivingDomain γ T) := by
    intro z hz v hv he
    calc
      z = F T (G T z) := (hw.2.2.2.2.2.2.2.1 T z hz).symm
      _ = F T (G T v) := congrArg (F T) he
      _ = v := hw.2.2.2.2.2.2.2.1 T v hv
  have htip : γ T ∉ survivingDomain γ T := by
    intro hh
    exact hh.1.2 (mem_image_of_mem γ ⟨zero_le, le_rfl⟩)
  obtain ⟨q, hq, hqH, hqeq⟩ := map_out_simple_access_path
    (survivingDomain γ T) (isOpen_survivingDomain hw.1 T) (G T)
    (hw.2.2.2.1 T).continuousOn hgi (hw.2.2.2.2.2.1 T)
    (γ T) w (U T) htip
    (hw.fresh_tip_chart_tendsto hU hT
      (tip_survives_prior_of_strict_height γ T hheight hfirst)) p hp hpD
  refine ⟨q, hq, hqH, ?_⟩
  intro t ht
  rw [hqeq t ht, sub_add_cancel]
  exact hw.2.2.2.2.2.2.2.1 T (p t) (hpD t ht)

end SLEExactGauge

end

end OAI
