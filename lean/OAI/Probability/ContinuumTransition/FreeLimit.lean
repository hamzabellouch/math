import OAI.Probability.ContinuumTransition.LowerLimit

namespace OAI

section
open scoped Topology
open Filter Set
namespace ContinuumTemperature

lemma core_pressure_nonneg {t β : ℝ} (ht : 1 < t) (hβ : 0 ≤ β) (h : ℝ) :
    0 ≤ physicalPressure (coreProfile t) t (β,h) := by
  exact div_nonneg (canonicalPressure_nonneg
    (measurable_radialPotential (measurable_coreProfile t)) ht hβ
    (coreProfile_stable_zero t) (fun _ _ => le_refl _)) (by linarith)

theorem core_pressure_tendsto {β : ℝ} (hβ : 0 < β) (h : ℝ) :
    Tendsto (fun t : ℝ => physicalPressure (coreProfile t) t (β,h))
      atTop (𝓝 (idealCorePressure h)) := by
  refine tendsto_order.2 ⟨?_,?_⟩
  · intro c hc
    unfold idealCorePressure at hc
    rcases lt_max_iff.mp hc with hc | hc
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      exact hc.trans_le (core_pressure_nonneg ht hβ.le h)
    · rcases lt_max_iff.mp hc with hc | hc
      · obtain ⟨η,hη,he⟩ := exists_packing_dilate_lt hc
        exact core_one_lower_eventually hβ.le hη h he
      · have hc' : c < packingDensity*(4*h-9) := by nlinarith only [hc]
        obtain ⟨η,hη,he⟩ := exists_packing_dilate_lt hc'
        exact core_tetra_lower_eventually hβ.le hη h he
  · intro c hc
    have hsep : ∀ᶠ t : ℝ in atTop, 2*(1+shellDelta)*Real.exp (-t) < 1 := by
      have hh := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (2*(1+shellDelta))
      simp only [mul_zero] at hh
      exact hh.eventually_lt_const zero_lt_one
    filter_upwards [(core_upper_bound_tendsto hβ h).eventually_lt_const hc,
      eventually_gt_atTop (1 : ℝ),hsep] with t ht h1 hs
    exact (core_pressure_upper h1 hβ.le hs h).trans_lt ht

end ContinuumTemperature
end

end OAI
