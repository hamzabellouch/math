import OAI.Geometry.IsometricImmersion.Calculus.SmoothMetricJet
import OAI.Geometry.IsometricImmersion.Darboux.SixVariableDarboux
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Matrix.Normed

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

abbrev MetricPInput := MetricMatrix × (MetricFirstJet × (MetricSecondJet × DarbouxState))

def universalConnection (a : MetricPInput) (i j : Fin 2) : ℝ :=
  ∑ k, christoffelJet a.1 a.2.1 k i j * stateGradient a.2.2.2 k

def universalDenominator (a : MetricPInput) : ℝ :=
  a.2.2.2 5 - universalConnection a 1 1

def universalEnergy (a : MetricPInput) : ℝ :=
  a.1.det - (a.1 1 1 * (stateGradient a.2.2.2 0)^2 -
    (a.1 0 1 + a.1 1 0) * stateGradient a.2.2.2 0 * stateGradient a.2.2.2 1 +
    a.1 0 0 * (stateGradient a.2.2.2 1)^2)

def universalMetricP (a : MetricPInput) : ℝ :=
  universalConnection a 0 0 +
    ((a.2.2.2 4 - universalConnection a 0 1)^2 +
      curvatureJet a.1 a.2.1 a.2.2.1 * universalEnergy a) / universalDenominator a

def universalMetricBase : Set MetricPInput := {a | a.1.det ≠ 0}
def universalMetricDomain : Set MetricPInput :=
  {a | a.1.det ≠ 0 ∧ universalDenominator a ≠ 0}

def metricPBundle (g : MetricField) (w : DarbouxState) : MetricPInput :=
  (g (statePoint w),
    ((fun d i j => coordPartial d (fun p => g p i j) (statePoint w)),
      ((fun d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w)), w)))

theorem universalConnection_metricPBundle (g : MetricField) (w : DarbouxState)
    (i j : Fin 2) :
    universalConnection (metricPBundle g w) i j = stateConnection g i j w := rfl

theorem universalDenominator_metricPBundle (g : MetricField) (w : DarbouxState) :
    universalDenominator (metricPBundle g w) = stateDenominator g w := rfl

theorem universalEnergy_metricPBundle (g : MetricField) (w : DarbouxState) :
    universalEnergy (metricPBundle g w) = stateEnergy g w := rfl

theorem sixVariableP_eq_universalMetricP {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    sixVariableP g w = universalMetricP (metricPBundle g w) := by
  have hK := gaussianCurvature_eq_curvatureJet hg hU hw
  unfold sixVariableP solvedDarboux jetNumerator jetMixed jetYY
  unfold universalMetricP
  rw [universalConnection_metricPBundle, universalConnection_metricPBundle,
    universalDenominator_metricPBundle, universalEnergy_metricPBundle]
  simp only [stateConnection, stateDenominator, stateEnergy, jetYY, metricPBundle, hK]

theorem universalMetricDet_contDiff :
    ContDiff ℝ ∞ (fun a : MetricPInput => a.1.det) := by
  simp only [Matrix.det_fin_two]
  fun_prop

theorem universalMetricBase_isOpen : IsOpen universalMetricBase :=
  isOpen_ne_fun universalMetricDet_contDiff.continuous continuous_const

theorem universalConnection_contDiffAt {a : MetricPInput}
    (ha : a ∈ universalMetricBase) (i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun b => universalConnection b i j) a := by
  have hΓ (k : Fin 2) :
      ContDiffAt ℝ ∞ (fun b : MetricPInput => christoffelJet b.1 b.2.1 k i j) a :=
    christoffelJet_contDiffAt (fun i j => by fun_prop)
      (fun d i j => by fun_prop) ha k i j
  have hv (k : Fin 2) :
      ContDiffAt ℝ ∞ (fun b : MetricPInput => stateGradient b.2.2.2 k) a :=
    ((contDiff_apply ℝ ℝ k).comp
      (stateGradient_contDiff.comp (by fun_prop))).contDiffAt
  simp only [universalConnection, Fin.sum_univ_two]
  exact ((hΓ 0).mul (hv 0)).add ((hΓ 1).mul (hv 1))

theorem universalDenominator_contDiffOn :
    ContDiffOn ℝ ∞ universalDenominator universalMetricBase := by
  intro a ha
  exact ((show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 5) a by fun_prop).sub
    (universalConnection_contDiffAt ha 1 1)).contDiffWithinAt

theorem universalMetricDomain_isOpen : IsOpen universalMetricDomain := by
  exact universalDenominator_contDiffOn.continuousOn.isOpen_inter_preimage
    universalMetricBase_isOpen isClosed_singleton.isOpen_compl

theorem universalEnergy_contDiff : ContDiff ℝ ∞ universalEnergy := by
  unfold universalEnergy stateGradient
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [Matrix.det_fin_two]
  fun_prop

theorem universalMetricP_contDiffOn :
    ContDiffOn ℝ ∞ universalMetricP universalMetricDomain := by
  intro a ha
  have hΓ := universalConnection_contDiffAt ha.1
  have hK : ContDiffAt ℝ ∞
      (fun b : MetricPInput => curvatureJet b.1 b.2.1 b.2.2.1) a :=
    curvatureJet_contDiffAt (fun i j => by fun_prop)
      (fun d i j => by fun_prop) (fun d e i j => by fun_prop) ha.1
  have hm : ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 4 - universalConnection b 0 1) a :=
    (show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 4) a by fun_prop).sub (hΓ 0 1)
  exact ((hΓ 0 0).add (((hm.pow 2).add (hK.mul universalEnergy_contDiff.contDiffAt)).div
    (universalDenominator_contDiffOn.contDiffAt (universalMetricBase_isOpen.mem_nhds ha.1))
    ha.2)).contDiffWithinAt

def universalMetricBaseTube (M d : ℝ) : Set MetricPInput :=
  Metric.closedBall 0 M ∩ (fun a : MetricPInput => |a.1.det|) ⁻¹' Ici d

def universalMetricTube (M d c : ℝ) : Set MetricPInput :=
  universalMetricBaseTube M d ∩ universalDenominator ⁻¹' {x : ℝ | c ≤ |x|}

theorem universalMetricBaseTube_isCompact (M d : ℝ) :
    IsCompact (universalMetricBaseTube M d) :=
  (isCompact_closedBall (0 : MetricPInput) M).inter_right
    (isClosed_Ici.preimage universalMetricDet_contDiff.continuous.abs)

theorem universalMetricBaseTube_subset_base (M : ℝ) {d : ℝ} (hd : 0 < d) :
    universalMetricBaseTube M d ⊆ universalMetricBase := by
  intro a ha hz
  have hh : d ≤ |a.1.det| := ha.2
  rw [hz, abs_zero] at hh
  linarith

theorem universalMetricTube_isCompact (M : ℝ) {d : ℝ} (hd : 0 < d) (c : ℝ) :
    IsCompact (universalMetricTube M d c) := by
  have hbase := universalMetricBaseTube_isCompact M d
  have hc : ContinuousOn universalDenominator (universalMetricBaseTube M d) :=
    universalDenominator_contDiffOn.continuousOn.mono (universalMetricBaseTube_subset_base M hd)
  have hclosed : IsClosed (universalMetricTube M d c) :=
    hc.preimage_isClosed_of_isClosed hbase.isClosed (isClosed_le continuous_const continuous_abs)
  exact hbase.of_isClosed_subset hclosed inter_subset_left

theorem universalMetricTube_subset_domain (M : ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    universalMetricTube M d c ⊆ universalMetricDomain := by
  intro a ha
  refine ⟨universalMetricBaseTube_subset_base M hd ha.1, ?_⟩
  intro hz
  have hh : c ≤ |universalDenominator a| := ha.2
  rw [hz, abs_zero] at hh
  linarith

theorem universalMetricTube_finite_P_bounds (M : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ N, ∀ a ∈ universalMetricTube M d c,
      ‖iteratedFDeriv ℝ k universalMetricP a‖ ≤ C := by
  classical
  have hk : ∀ k : Fin (N + 1), ∃ A : ℝ,
      ∀ a ∈ universalMetricTube M d c, ‖iteratedFDeriv ℝ k.val universalMetricP a‖ ≤ A := by
    intro k
    have hcont : ContinuousOn (iteratedFDeriv ℝ k.val universalMetricP) universalMetricDomain := by
      apply (universalMetricP_contDiffOn.continuousOn_iteratedFDerivWithin
        (WithTop.coe_le_coe.mpr le_top) universalMetricDomain_isOpen.uniqueDiffOn).congr
      intro a ha
      exact (iteratedFDerivWithin_eq_iteratedFDeriv universalMetricDomain_isOpen.uniqueDiffOn
        ((universalMetricP_contDiffOn.contDiffAt
          (universalMetricDomain_isOpen.mem_nhds ha)).of_le (WithTop.coe_le_coe.mpr le_top)) ha).symm
    exact (universalMetricTube_isCompact M hd c).exists_bound_of_continuousOn
      (hcont.mono (universalMetricTube_subset_domain M hd hc))
  choose A hA using hk
  refine ⟨∑ k : Fin (N + 1), |A k|, Finset.sum_nonneg (fun k hk => abs_nonneg _), ?_⟩
  intro k hk a ha
  let j : Fin (N + 1) := ⟨k, by omega⟩
  exact (hA j a ha).trans ((le_abs_self (A j)).trans
    (Finset.single_le_sum (fun i hi => abs_nonneg (A i)) (Finset.mem_univ j)))

end SmoothLocal.HighEquation

end

end OAI
