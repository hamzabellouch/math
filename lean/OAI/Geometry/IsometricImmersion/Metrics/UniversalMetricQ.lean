import OAI.Geometry.IsometricImmersion.Darboux.QSpatialRestriction

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def universalQDenominator (a : MetricPInput) : ℝ :=
  a.2.2.2 5 - universalConnection a 0 0

def universalMetricQ (a : MetricPInput) : ℝ :=
  universalConnection a 1 1 +
    ((a.2.2.2 4 - universalConnection a 0 1)^2 +
      curvatureJet a.1 a.2.1 a.2.2.1 * universalEnergy a) / universalQDenominator a

def universalMetricQDomain : Set MetricPInput :=
  {a | a.1.det ≠ 0 ∧ universalQDenominator a ≠ 0}

def universalMetricQTube (M d c : ℝ) : Set MetricPInput :=
  universalMetricBaseTube M d ∩ universalQDenominator ⁻¹' {x : ℝ | c ≤ |x|}

theorem universalQDenominator_metricPBundle (g : MetricField) (w : DarbouxState) :
    universalQDenominator (metricPBundle g w) = stateQDenominator g w := rfl

theorem sixVariableQ_eq_universalMetricQ {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    sixVariableQ g w = universalMetricQ (metricPBundle g w) := by
  rw [sixVariableQ_explicit hg hU hw]
  have hK := gaussianCurvature_eq_curvatureJet hg hU hw
  unfold solvedDarbouxQ jetNumerator jetMixed jetXX universalMetricQ
  rw [universalConnection_metricPBundle, universalConnection_metricPBundle,
    universalQDenominator_metricPBundle, universalEnergy_metricPBundle]
  simp only [stateConnection, stateQDenominator, stateEnergy, jetXX, metricPBundle, hK]

theorem universalQDenominator_contDiffOn :
    ContDiffOn ℝ ∞ universalQDenominator universalMetricBase := by
  intro a ha
  exact ((show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 5) a by fun_prop).sub
    (universalConnection_contDiffAt ha 0 0)).contDiffWithinAt

theorem universalMetricQDomain_isOpen : IsOpen universalMetricQDomain :=
  universalQDenominator_contDiffOn.continuousOn.isOpen_inter_preimage
    universalMetricBase_isOpen isClosed_singleton.isOpen_compl

theorem universalMetricQ_contDiffOn :
    ContDiffOn ℝ ∞ universalMetricQ universalMetricQDomain := by
  intro a ha
  have hΓ := universalConnection_contDiffAt ha.1
  have hK : ContDiffAt ℝ ∞
      (fun b : MetricPInput => curvatureJet b.1 b.2.1 b.2.2.1) a :=
    curvatureJet_contDiffAt (fun i j => by fun_prop)
      (fun d i j => by fun_prop) (fun d e i j => by fun_prop) ha.1
  have hm : ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 4 - universalConnection b 0 1) a :=
    (show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 4) a by fun_prop).sub (hΓ 0 1)
  exact ((hΓ 1 1).add (((hm.pow 2).add (hK.mul universalEnergy_contDiff.contDiffAt)).div
    (universalQDenominator_contDiffOn.contDiffAt (universalMetricBase_isOpen.mem_nhds ha.1))
    ha.2)).contDiffWithinAt

theorem universalMetricQTube_isCompact (M : ℝ) {d : ℝ} (hd : 0 < d) (c : ℝ) :
    IsCompact (universalMetricQTube M d c) := by
  have hbase := universalMetricBaseTube_isCompact M d
  have hc : ContinuousOn universalQDenominator (universalMetricBaseTube M d) :=
    universalQDenominator_contDiffOn.continuousOn.mono (universalMetricBaseTube_subset_base M hd)
  have hclosed : IsClosed (universalMetricQTube M d c) :=
    hc.preimage_isClosed_of_isClosed hbase.isClosed (isClosed_le continuous_const continuous_abs)
  exact hbase.of_isClosed_subset hclosed inter_subset_left

theorem universalMetricQTube_subset_domain (M : ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    universalMetricQTube M d c ⊆ universalMetricQDomain := by
  intro a ha
  refine ⟨universalMetricBaseTube_subset_base M hd ha.1, ?_⟩
  intro hz
  have hh : c ≤ |universalQDenominator a| := ha.2
  rw [hz, abs_zero] at hh
  linarith

theorem universalMetricQTube_finite_bounds (M : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ N, ∀ a ∈ universalMetricQTube M d c,
      ‖iteratedFDeriv ℝ k universalMetricQ a‖ ≤ C := by
  classical
  have hk : ∀ k : Fin (N + 1), ∃ A : ℝ,
      ∀ a ∈ universalMetricQTube M d c, ‖iteratedFDeriv ℝ k.val universalMetricQ a‖ ≤ A := by
    intro k
    have hcont : ContinuousOn (iteratedFDeriv ℝ k.val universalMetricQ) universalMetricQDomain := by
      apply (universalMetricQ_contDiffOn.continuousOn_iteratedFDerivWithin
        (WithTop.coe_le_coe.mpr le_top) universalMetricQDomain_isOpen.uniqueDiffOn).congr
      intro a ha
      exact (iteratedFDerivWithin_eq_iteratedFDeriv universalMetricQDomain_isOpen.uniqueDiffOn
        ((universalMetricQ_contDiffOn.contDiffAt
          (universalMetricQDomain_isOpen.mem_nhds ha)).of_le (WithTop.coe_le_coe.mpr le_top)) ha).symm
    exact (universalMetricQTube_isCompact M hd c).exists_bound_of_continuousOn
      (hcont.mono (universalMetricQTube_subset_domain M hd hc))
  choose A hA using hk
  refine ⟨∑ k : Fin (N + 1), |A k|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro k hk a ha
  let j : Fin (N + 1) := ⟨k, by omega⟩
  exact (hA j a ha).trans ((le_abs_self (A j)).trans
    (Finset.single_le_sum (fun index _ => abs_nonneg (A index)) (Finset.mem_univ j)))

end SmoothLocal.HighEquation

end

end OAI
