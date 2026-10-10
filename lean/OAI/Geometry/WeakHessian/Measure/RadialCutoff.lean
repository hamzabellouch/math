import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma exists_probability_reference (m : Measure X) (o : X) (hm : m ≠ 0)
    (hfinite : ∀ B : Set X, Bornology.IsBounded B → m B < ∞) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ ν ≪ m ∧ m ≪ ν ∧
      (∃ C : ℝ≥0, ν ≤ (C:ℝ≥0∞) • m) ∧
      ∀ B : Set X, Bornology.IsBounded B → ∃ C : ℝ≥0, m.restrict B ≤ (C:ℝ≥0∞) • ν := by
  let B : ℕ → Set X := fun n => Metric.ball o (n+1)
  obtain ⟨c,hc,hcs⟩ := ENNReal.exists_pos_tsum_mul_lt_of_countable
    (by norm_num : (1:ℝ≥0∞) ≠ 0) (fun n : ℕ => 1+m (B n))
    (fun n => ENNReal.add_ne_top.mpr ⟨by simp,(hfinite _ Metric.isBounded_ball).ne⟩)
  let μ : Measure X := Measure.sum (fun n => (c n:ℝ≥0∞) • m.restrict (B n))
  have hsum : (∑' n,(c n:ℝ≥0∞)) < 1 := (ENNReal.tsum_le_tsum fun n => by
    calc (c n:ℝ≥0∞) = 1*(c n:ℝ≥0∞) := by simp
         _ ≤ (1+m (B n))*(c n:ℝ≥0∞) := by gcongr; exact le_add_right le_rfl).trans_lt hcs
  have hμ : μ ≤ m := by
    apply Measure.le_iff.mpr
    intro s hs
    rw [show μ s = ∑' n,(c n:ℝ≥0∞)*(m.restrict (B n)) s by
      simp only [μ,Measure.sum_apply _ hs,Measure.smul_apply,smul_eq_mul]]
    calc
      _ ≤ ∑' n,(c n:ℝ≥0∞)*m s := ENNReal.tsum_le_tsum fun n => by
        gcongr; exact Measure.restrict_le_self
      _ = (∑' n,(c n:ℝ≥0∞))*m s := by rw [ENNReal.tsum_mul_right]
      _ ≤ 1*m s := by gcongr
      _ = m s := one_mul _
  have hμfin : μ univ < ∞ := by
    have H : μ univ ≤ ∑' n,(1+m (B n))*(c n:ℝ≥0∞) := by
      simp only [μ,Measure.sum_apply _ MeasurableSet.univ,Measure.smul_apply,
        smul_eq_mul,Measure.restrict_apply_univ]
      apply ENNReal.tsum_le_tsum
      intro n
      calc (c n:ℝ≥0∞)*m (B n) = m (B n)*(c n:ℝ≥0∞) := mul_comm _ _
           _ ≤ (1+m (B n))*(c n:ℝ≥0∞) := by gcongr; exact le_add_left le_rfl
    exact H.trans_lt (hcs.trans (by simp))
  have hloc (n : ℕ) : m.restrict (B n) ≤ (c n:ℝ≥0∞)⁻¹ • μ := by
    calc m.restrict (B n) = (c n:ℝ≥0∞)⁻¹ • ((c n:ℝ≥0∞) • m.restrict (B n)) := by
           rw [smul_smul,ENNReal.inv_mul_cancel (by exact_mod_cast (hc n).ne') ENNReal.coe_ne_top,one_smul]
         _ ≤ (c n:ℝ≥0∞)⁻¹ • μ := by
           gcongr
           exact Measure.le_sum (fun index => (c index:ℝ≥0∞) • m.restrict (B index)) n
  have hmμ : m ≪ μ := by
    intro s hs
    have hBn (n : ℕ) : m (s ∩ B n) = 0 := by
      have H := (Measure.absolutelyContinuous_of_le_smul (hloc n)) hs
      rw [Measure.restrict_apply' (show MeasurableSet (B n) from Metric.isOpen_ball.measurableSet)] at H
      exact H
    rw [show s = ⋃ n,s ∩ B n by
      rw [← inter_iUnion,show (⋃ n,B n)=univ from Metric.iUnion_ball_nat_succ o,inter_univ]]
    exact measure_iUnion_null hBn
  have hμne : μ ≠ 0 := by
    intro hz
    apply hm
    exact Measure.absolutelyContinuous_zero_iff.mp (hz ▸ hmμ)
  let : IsFiniteMeasure μ := ⟨hμfin⟩
  let : NeZero μ := ⟨hμne⟩
  let ν : Measure X := (μ univ)⁻¹ • μ
  have hνm : ν ≤ (μ univ)⁻¹ • m := by dsimp [ν]; gcongr
  have hμν : μ = μ univ • ν := by
    simp only [ν,smul_smul,ENNReal.mul_inv_cancel (NeZero.ne (μ univ)) hμfin.ne,one_smul]
  refine ⟨ν,inferInstance,Measure.absolutelyContinuous_of_le_smul hνm,
    hmμ.trans ?_,?_,?_⟩
  · rw [hμν]
    exact Measure.smul_absolutelyContinuous
  · refine ⟨((μ univ)⁻¹).toNNReal,?_⟩
    simpa only [ENNReal.coe_toNNReal (ENNReal.inv_ne_top.mpr (NeZero.ne _))] using hνm
  · intro A hA
    obtain ⟨R,hR⟩ := hA.subset_ball o
    obtain ⟨n,hn⟩ := exists_nat_gt R
    have hAB : A ⊆ B n := hR.trans (Metric.ball_subset_ball (by exact le_trans hn.le (by linarith)))
    have H : m.restrict A ≤ ((c n:ℝ≥0∞)⁻¹*μ univ) • ν := by
      calc m.restrict A ≤ m.restrict (B n) := Measure.restrict_mono hAB le_rfl
           _ ≤ (c n:ℝ≥0∞)⁻¹ • μ := hloc n
           _ = (c n:ℝ≥0∞)⁻¹ • (μ univ • ν) := congrArg (fun ρ : Measure X => (c n:ℝ≥0∞)⁻¹ • ρ) hμν
           _ = _ := smul_smul _ _ _
    have hC : (c n:ℝ≥0∞)⁻¹*μ univ ≠ ∞ := ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast (hc n).ne')) hμfin.ne
    exact ⟨((c n:ℝ≥0∞)⁻¹*μ univ).toNNReal,by simpa only [ENNReal.coe_toNNReal hC] using H⟩
end WeakHessian

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace WeakHessian
variable {X : Type*} [MetricSpace X]
def radialCutoff (o : X) (n : ℕ) (x : X) : ℝ := max 0 (1-dist x o/((n:ℝ)+1))
lemma radialCutoff_nonneg (o : X) (n : ℕ) (x : X) : 0 ≤ radialCutoff o n x := le_max_left _ _
lemma radialCutoff_le_one (o : X) (n : ℕ) (x : X) : radialCutoff o n x ≤ 1 := by
  apply max_le zero_le_one
  have H : 0 ≤ dist x o/((n:ℝ)+1) := by positivity
  linarith
lemma radialCutoff_lipschitz (o : X) (n : ℕ) :
    LipschitzWith (((n:ℝ≥0)+1)⁻¹) (radialCutoff o n) := by
  apply LipschitzWith.const_max _ 0
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have ha : 0 < (n:ℝ)+1 := by positivity
  simp only [NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,Real.dist_eq]
  rw [show (1-dist x o/((n:ℝ)+1))-(1-dist y o/((n:ℝ)+1)) =
      (dist y o-dist x o)/((n:ℝ)+1) by ring,abs_div,abs_of_pos ha,inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (by simpa only [dist_comm] using abs_dist_sub_le y x o) ha.le
lemma radialCutoff_compact [ProperSpace X] (o : X) (n : ℕ) :
    HasCompactSupport (radialCutoff o n) := by
  apply HasCompactSupport.intro (isCompact_closedBall o ((n:ℝ)+1))
  intro x hx
  have H : (n:ℝ)+1 < dist x o := lt_of_not_ge hx
  apply max_eq_left
  have : 1 < dist x o/((n:ℝ)+1) := (lt_div_iff₀ (by positivity)).mpr (by simpa using H)
  linarith
lemma radialCutoff_tendsto (o : X) (x : X) :
    Tendsto (fun n => radialCutoff o n x) atTop (𝓝 1) := by
  have H := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (dist x o)
  have HH : Tendsto (fun n : ℕ => 1-dist x o/((n:ℝ)+1)) atTop (𝓝 1) := by
    simpa only [mul_one_div,mul_zero,sub_zero] using tendsto_const_nhds.sub H
  simpa only [radialCutoff,max_eq_right zero_le_one] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)).max HH
end WeakHessian

end

end OAI
