import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.BarrierInitialDeterministicBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.OwnProbabilityFieldCapBarrier
import OAI.Analysis.CoulombIonization.Localization.PosteriorSubmeanBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.SpatialCapSubmeanBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric

namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma originalQueryField_joint_measurable {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s) :
    Measurable (fun p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) × Space =>
      originalQueryField F Z lam r j c₁ r₀ s p.1 p.2) := by
  have hm := originalMasterField_measurable (graphRawLaw F)
    (fun k : Fin K => dyadicObservationWidth r k) j hc hr₀ hs canonicalRealPacket_smooth.continuous
  exact ((measurable_const.div measurable_snd.norm).sub measurable_const).sub
    (potential_joint_measurable hm)

lemma originalQueryField_continuousOn_annulus {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    {u : ℝ} (hu : 0 < u) :
    ContinuousOn (originalQueryField F Z lam r j c₁ r₀ s z) (closedAnnularShell u (2*u)) := by
  obtain ⟨M,hM,hρ⟩ := originalQueryDensity_bounded_L1 F r j hc hr₀ hs hrs
  have hp := (bounded_L1_potential_lipschitz (hρ z).1 (hρ z).2.1 hM
    (hρ z).2.2.1 (hρ z).2.2.2).continuous
  apply ((continuousOn_const.div continuous_norm.continuousOn ?_).sub continuousOn_const).sub hp.continuousOn
  intro x hx
  exact ne_of_gt (hu.trans_le hx.1)

lemma original_capBand_excess_prod_integrable {N K : ℕ} (F : fermionGraph N)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (r : ℝ) (j : ℕ)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s)
    {u C : ℝ} (hu : 0 < u) (hC : 0 ≤ C) :
    Integrable (fun p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) × Space =>
      max ((u/100000)^4*originalQueryField F Z lam r j c₁ r₀ s p.1 p.2-C) 0)
      ((physicalObservationLaw (graphRawLaw F) K).prod
        (volume.restrict (closedAnnularShell u (2*u)))) := by
  have hAc := closedAnnularShell_compact u (2*u)
  let : IsFiniteMeasure (volume.restrict (closedAnnularShell u (2*u))) :=
    isFiniteMeasure_restrict.mpr hAc.measure_ne_top
  have hm := originalQueryField_joint_measurable (K := K) F Z lam r j hc hr₀ hs
  apply Integrable.of_bound ((hm.const_mul _).sub measurable_const |>.max measurable_const).aestronglyMeasurable
    ((u/100000)^4*(Z/u))
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hAc.measurableSet)] with p hp
  rw [Real.norm_of_nonneg (le_max_right _ _)]
  apply max_le
  · have hq := originalQueryField_le_nuclear F Z r hlam j c₁ r₀ s p.1 p.2
    have hz : Z/‖p.2‖ ≤ Z/u := div_le_div_of_nonneg_left hZ hu hp.1
    have hh := mul_le_mul_of_nonneg_left (hq.trans hz) (show 0 ≤ (u/100000)^4 by positivity)
    change (u/100000)^4*originalQueryField F Z lam r j c₁ r₀ s p.1 p.2-C ≤ _
    linarith only [hh,hC]
  · positivity

lemma original_capBandStatistic_measurable {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s)
    (u C : ℝ) :
    Measurable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
      capBandStatistic u C (originalQueryField F Z lam r j c₁ r₀ s z)) := by
  have hm := originalQueryField_joint_measurable (K := K) F Z lam r j hc hr₀ hs
  exact (((hm.const_mul _).sub measurable_const).max measurable_const).stronglyMeasurable.integral_prod_right'.measurable.const_mul _

theorem original_capBandStatistic_controls_field {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    {u C : ℝ} (hu : 0 < u) (hC : 0 ≤ C)
    (hstat : capBandStatistic u C (originalQueryField F Z lam r j c₁ r₀ s z) ≤ 1) :
    ∀ y, 5*u/4 ≤ ‖y‖ → ‖y‖ ≤ 7*u/4 →
      (localCellRadius y)^4*originalQueryField F Z lam r j c₁ r₀ s z y ≤ 16*(C+1) := by
  apply capBandStatistic_simultaneous_cap hu hC
    (originalQueryField_continuousOn_annulus F Z lam r j hc hr₀ hs hrs z hu) _ hstat
  intro y hyl _
  exact originalQueryField_ball_submean F Z lam r j hc hr₀ hs hrs z (by positivity) y (by linarith)

end CoulombAtom

end

end OAI
