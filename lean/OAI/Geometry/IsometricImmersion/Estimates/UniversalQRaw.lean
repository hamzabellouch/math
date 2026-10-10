import OAI.Geometry.IsometricImmersion.Metrics.UniversalMetricQ
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def universalQCurvature (a : MetricPInput) : ℝ :=
  curvatureJet a.1 a.2.1 a.2.2.1

def universalQNumerator (a : MetricPInput) : ℝ :=
  (a.2.2.2 4 - universalConnection a 0 1)^2 +
    universalQCurvature a * universalEnergy a

def universalQRaw (a : MetricPInput) : Fin 4 → ℝ :=
  ![universalQDenominator a, universalEnergy a,
    universalQNumerator a, universalQCurvature a]

theorem universalQCurvature_metricPBundle {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    universalQCurvature (metricPBundle g w) = gaussianCurvature g (statePoint w) :=
  (gaussianCurvature_eq_curvatureJet hg hU hw).symm

theorem universalQNumerator_metricPBundle {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    universalQNumerator (metricPBundle g w) = stateNumerator g w := by
  unfold universalQNumerator
  rw [universalQCurvature_metricPBundle hg hU hw, universalEnergy_metricPBundle,
    universalConnection_metricPBundle]
  rfl

theorem universalQCurvature_contDiffOn :
    ContDiffOn ℝ ∞ universalQCurvature universalMetricBase := by
  intro a ha
  exact (curvatureJet_contDiffAt (fun i j => by fun_prop)
    (fun d i j => by fun_prop) (fun d e i j => by fun_prop) ha).contDiffWithinAt

theorem universalQNumerator_contDiffOn :
    ContDiffOn ℝ ∞ universalQNumerator universalMetricBase := by
  intro a ha
  have hm : ContDiffAt ℝ ∞
      (fun b : MetricPInput => b.2.2.2 4 - universalConnection b 0 1) a :=
    (show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 4) a by fun_prop).sub
      (universalConnection_contDiffAt ha 0 1)
  exact ((hm.pow 2).add
    ((universalQCurvature_contDiffOn.contDiffAt (universalMetricBase_isOpen.mem_nhds ha)).mul
      universalEnergy_contDiff.contDiffAt)).contDiffWithinAt

theorem universalQRaw_contDiffOn :
    ContDiffOn ℝ ∞ universalQRaw universalMetricBase := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact universalQDenominator_contDiffOn
  · exact universalEnergy_contDiff.contDiffOn
  · exact universalQNumerator_contDiffOn
  · exact universalQCurvature_contDiffOn

theorem universalQRaw_uniform_error (M : ℝ) {d error : ℝ}
    (hd : 0 < d) (he : 0 < error) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ a ∈ universalMetricBaseTube M d,
      ∀ b ∈ universalMetricBaseTube M d, ‖b - a‖ ≤ epsilon →
        ∀ i : Fin 4, |universalQRaw b i - universalQRaw a i| ≤ error := by
  have hc := (universalMetricBaseTube_isCompact M d).uniformContinuousOn_of_continuous
    (universalQRaw_contDiffOn.continuousOn.mono (universalMetricBaseTube_subset_base M hd))
  obtain ⟨epsilon, hepsilon, herror⟩ := Metric.uniformContinuousOn_iff_le.mp hc error he
  refine ⟨epsilon, hepsilon, ?_⟩
  intro a ha b hb hab i
  have hn : ‖universalQRaw b - universalQRaw a‖ ≤ error := by
    simpa only [dist_eq_norm] using herror b hb a ha (by simpa only [dist_eq_norm] using hab)
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    (norm_le_pi_norm (universalQRaw b - universalQRaw a) i).trans hn

theorem universalQDenominator_uniform_bound (M : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ a ∈ universalMetricBaseTube M d,
      |universalQDenominator a| ≤ A := by
  obtain ⟨C, hC⟩ := (universalMetricBaseTube_isCompact M d).exists_bound_of_continuousOn
    (universalQDenominator_contDiffOn.continuousOn.mono
      (universalMetricBaseTube_subset_base M hd))
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro a ha
  simpa only [Real.norm_eq_abs] using (hC a ha).trans (le_max_right 1 C)

theorem universalQRaw_uniform_margins (M : ℝ) {d nu eta beta kappa : ℝ}
    (hd : 0 < d) (hnu : 0 < nu) (heta : 0 < eta) (hbeta : 0 < beta)
    (hkappa : 0 < kappa) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ a ∈ universalMetricBaseTube M d,
      ∀ b ∈ universalMetricBaseTube M d, ‖b - a‖ ≤ epsilon →
      nu ≤ |universalQDenominator a| → eta ≤ universalEnergy a →
      universalQNumerator a ≤ -beta → universalQCurvature a ≤ -kappa →
      nu / 2 ≤ |universalQDenominator b| ∧ eta / 2 ≤ universalEnergy b ∧
      universalQNumerator b ≤ -(beta / 2) ∧ universalQCurvature b ≤ -(kappa / 2) := by
  let error := min (nu / 2) (min (eta / 2) (min (beta / 2) (kappa / 2)))
  have he : 0 < error := lt_min (half_pos hnu)
    (lt_min (half_pos heta) (lt_min (half_pos hbeta) (half_pos hkappa)))
  obtain ⟨epsilon, hepsilon, herror⟩ := universalQRaw_uniform_error M hd he
  refine ⟨epsilon, hepsilon, ?_⟩
  intro a ha b hb hab hden henergy hnum hK
  have h0 := herror a ha b hb hab 0
  have h1 := herror a ha b hb hab 1
  have h2 := herror a ha b hb hab 2
  have h3 := herror a ha b hb hab 3
  change |universalQDenominator b - universalQDenominator a| ≤ error at h0
  change |universalEnergy b - universalEnergy a| ≤ error at h1
  change |universalQNumerator b - universalQNumerator a| ≤ error at h2
  change |universalQCurvature b - universalQCurvature a| ≤ error at h3
  have he0 : error ≤ nu / 2 := min_le_left _ _
  have he1 : error ≤ eta / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have he2 : error ≤ beta / 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have he3 : error ≤ kappa / 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hdenerror := (abs_sub_abs_le_abs_sub (universalQDenominator a)
    (universalQDenominator b)).trans (by simpa only [abs_sub_comm] using h0)
  exact ⟨by linarith, by linarith [(abs_le.mp h1).1],
    by linarith [(abs_le.mp h2).2], by linarith [(abs_le.mp h3).2]⟩

end SmoothLocal.HighEquation

end

end OAI
