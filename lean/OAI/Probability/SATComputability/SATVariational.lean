import OAI.Probability.SATComputability.InterpolationUpper
import OAI.Probability.SATComputability.ReplicaPositivity
import OAI.Probability.SATComputability.RationalHierarchy
import OAI.Probability.SATComputability.RelaxedPressure
import OAI.Probability.SATComputability.ExponentContinuity
import OAI.Probability.DilutedSpin.SymmetricTrialLower

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

noncomputable def satPressure (a : ℝ≥0) (β : ℝ) : ℝ :=
  liminf (pressure (satModel a β)) atTop

theorem satPressure_tendsto {a : ℝ≥0} (ha : 0 < a) {β : ℝ} (hβ : 0 < β) :
    Tendsto (pressure (satModel a β)) atTop (nhds (satPressure a β)) := by
  have hθ := satModel_interaction_integrable a hβ.le
  have hh := satModel_field_integrable a β
  have hb := pressure_bounded (satModel a β) hθ hh
  have hs : limsup (pressure (satModel a β)) atTop ≤ satPressure a β := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨r, ζ, m, hm, happrox⟩ := symmetric_trial_lower (satModel a β) ha
      hθ hh (satModel_symmetric a β) hε
    have hu : limsup (pressure (satModel a β)) atTop ≤ functional (satModel a β) r ζ m := by
      apply limsup_le_of_le hb.2.isCobounded_le
      filter_upwards [eventually_gt_atTop 0] with N hN
      let : NeZero N := ⟨Nat.ne_of_gt hN⟩
      exact PositiveInterpolation.pressure_le_functional (satModel a β)
        (satModel_interpolation_admissible ha hβ) r ζ m hm
    exact hu.trans happrox
  exact tendsto_of_le_liminf_of_limsup_le le_rfl hs hb.1 hb.2

theorem relaxedPressure_tendsto {a : ℝ≥0} (ha : 0 < a) {β : ℝ} (hβ : 0 < β) :
    Tendsto (relaxedPoissonPressure a β) atTop (nhds (satPressure a β)) := by
  have he : pressure (satModel a β) = relaxedPoissonPressure a β :=
    funext (satModel_pressure a β)
  rw [← he]
  exact satPressure_tendsto ha hβ

theorem satPressure_le_rational_trial {a : ℝ≥0} (ha : 0 < a) {β : ℝ} (hβ : 0 < β)
    (r : ℕ) (t : RationalTree (r+1)) (m : Fin r → ℝ) (hm : Exponents m) :
    satPressure a β ≤ functional (satModel a β) r (rationalTreeValue (r+1) t) m := by
  apply le_of_tendsto (satPressure_tendsto ha hβ)
  filter_upwards [eventually_gt_atTop 0] with N hN
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  exact PositiveInterpolation.finiteHierarchy_pressure_le (satModel a β)
    (satModel_interpolation_admissible ha hβ) r _ (rationalTreeValue_finite _ _) m hm

theorem exists_rational_trial_near_pressure {a : ℝ≥0} (ha : 0 < a) {β : ℝ} (hβ : 0 < β)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ) (t : RationalTree (r+1)) (m : Fin r → ℝ), Exponents m ∧
      functional (satModel a β) r (rationalTreeValue (r+1) t) m < satPressure a β + ε := by
  obtain ⟨r, ζ, m, hm, happrox⟩ := symmetric_trial_lower (satModel a β) ha
    (satModel_interaction_integrable a hβ.le) (satModel_field_integrable a β)
    (satModel_symmetric a β) (show 0 < ε/2 by positivity)
  have hc := functional_continuous (satModel a β) m (fun i => (hm.2 i).1)
    (satModel_interaction_integrable a hβ.le) (satModel_field_integrable a β)
  have hn : {η | functional (satModel a β) r η m < satPressure a β+ε} ∈ nhds ζ :=
    hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by
      change functional (satModel a β) r ζ m ≤ satPressure a β+ε/2 at happrox
      linarith))
  obtain ⟨η, hη, hη'⟩ := mem_closure_iff_nhds.mp ((rationalTreeValue_dense (r+1)) ζ) _ hn
  obtain ⟨t, rfl⟩ := hη'
  exact ⟨r, t, m, hm, hη⟩

theorem exists_fully_rational_trial_near_pressure {a : ℝ≥0} (ha : 0 < a)
    {β : ℝ} (hβ : 0 < β) {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ) (t : RationalTree (r+1)) (m : Fin r → ℚ),
      Exponents (fun i => (m i : ℝ)) ∧
      functional (satModel a β) r (rationalTreeValue (r+1) t) (fun i => (m i : ℝ)) <
        satPressure a β + ε := by
  obtain ⟨r, t, m, hm, ht⟩ := exists_rational_trial_near_pressure ha hβ hε
  have hc := functional_continuousAt_exponents (satModel a β)
    (satModel_interaction_integrable a hβ.le) (satModel_field_integrable a β)
    (rationalTreeValue (r+1) t) hm
  have hn : {m : Fin r → ℝ | functional (satModel a β) r
      (rationalTreeValue (r+1) t) m < satPressure a β + ε} ∈ nhds m :=
    hc.preimage_mem_nhds (Iio_mem_nhds ht)
  obtain ⟨q, hq, hv⟩ := exists_rational_exponents hm hn
  exact ⟨r, t, q, hq, hv⟩

theorem negative_pressure_has_rational_trial {a : ℝ≥0} (ha : 0 < a)
    {β : ℝ} (hβ : 0 < β) (hneg : satPressure a β < 0) :
    ∃ (r : ℕ) (t : RationalTree (r+1)) (m : Fin r → ℚ),
      Exponents (fun i => (m i : ℝ)) ∧
      functional (satModel a β) r (rationalTreeValue (r+1) t) (fun i => (m i : ℝ)) < 0 := by
  obtain ⟨r, t, m, hm, hv⟩ := exists_fully_rational_trial_near_pressure ha hβ (neg_pos.mpr hneg)
  exact ⟨r, t, m, hm, by simpa only [add_neg_cancel] using hv⟩

end FixedClauseThreshold.Computability

end OAI
