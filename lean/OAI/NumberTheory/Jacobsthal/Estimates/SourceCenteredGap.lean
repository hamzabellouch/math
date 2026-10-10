import OAI.NumberTheory.Jacobsthal.Analysis.PaperContinuousCorrection

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly ErdosBoundaryIntegral Erdos970Dependency.InvariantCostBound
open NumberTheoryLean.PrimeHistories NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.JacobsthalSourceScale

noncomputable def sourceRootGap (a z : ℝ) : ℝ :=
  Real.log (ErdosInverseBoxHeight.sourceY z : ℝ)/Real.log (ErdosInverseBoxHeight.sourceW z)-a+2

noncomputable def sourceRootNode (a z : ℝ) : Node where
  side := .even
  gap := sourceRootGap a z
  ratio := sourceRootGap a z/ErdosInverseBoxHeight.sourceB z
  cutoff := ErdosInverseBoxHeight.sourceB z
  closed := true

theorem sourceRoot_eq_paper (a : ℝ) {z : ℝ} (hz : 1 < z) (hW : 1 < sourceW (Real.log z)) :
    sourceRootNode a z=paperStart a floorRemainder true (Real.log z) := by
  have hg := paperGap_floor_eq a (L := Real.log z) hW
  rw [Real.exp_log (by linarith : 0 < z)] at hg
  change paperGap a floorRemainder (Real.log z)=sourceRootGap a z at hg
  unfold sourceRootNode paperStart
  rw [hg]
  rfl

theorem floored_source_prefactor_tendsto (a : ℝ) :
    Tendsto (fun z => (ErdosInverseBoxHeight.sourceB z)^2*
      phiEven (sourceRootNode a z).ratio/(sourceRootNode a z).gap^2) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  have ht := (paper_prefactor_tendsto a floorRemainder_tendsto).comp Real.tendsto_log_atTop
  apply ht.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually source_scale_eventually,eventually_gt_atTop (1:ℝ)] with z hs hz
  rw [sourceRoot_eq_paper a hz hs.1]
  rfl

theorem floored_source_correction_tendsto (a : ℝ) :
    Tendsto (fun z => (ErdosInverseBoxHeight.sourceB z)^2*
      continuousBoundaryCorrection (ErdosInverseBoxHeight.sourceW z) 2 (sourceRootNode a z)) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant*(2*signedCoefficientI/costMass))) := by
  have ht := paper_z_continuous_correction_tendsto a true floorRemainder_tendsto
  apply ht.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually source_scale_eventually,eventually_gt_atTop (1:ℝ)] with z hs hz
  rw [sourceRoot_eq_paper a hz hs.1]
  rfl

end ErdosCorrectionLimit

end

section

open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosSourceReferenceMargin
open ErdosCorrectionLimit
open NumberTheoryLean.JacobsthalSourceScale NumberTheoryLean.PrimeBinMembership

theorem log_sourceW_div_log_tendsto :
    Tendsto (fun L : ℝ => Real.log (sourceW L)/Real.log L) atTop (𝓝 1) := by
  have h0 : Tendsto (fun L : ℝ => Real.log (Real.log L)/Real.log L) atTop (𝓝 0) := by
    simpa only [Function.comp_def,id_eq] using! Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hh : Tendsto (fun L : ℝ => 1-2*(Real.log (Real.log L)/Real.log L)) atTop (𝓝 1) := by
    simpa only [mul_zero,sub_zero] using tendsto_const_nhds.sub (h0.const_mul 2)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with L hL
  have hL0 : L ≠ 0 := by linarith
  have hlog : Real.log L ≠ 0 := (Real.log_pos hL).ne'
  rw [sourceW,Real.log_div hL0 (pow_ne_zero 2 hlog),Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  field_simp

theorem log_div_log_sourceW_tendsto :
    Tendsto (fun L : ℝ => Real.log L/Real.log (sourceW L)) atTop (𝓝 1) := by
  have hh := log_sourceW_div_log_tendsto.inv₀ (by norm_num : (1:ℝ)≠0)
  simpa only [inv_one,inv_div] using! hh

theorem centered_paper_gap_tendsto (a : ℝ) :
    Tendsto (fun L => paperGap a floorRemainder L-2*sourceB L) atTop (𝓝 (-a)) := by
  have hc : Tendsto (fun _ : ℝ => -a+2) atTop (𝓝 (-a+2)) := tendsto_const_nhds
  have hh := (hc.sub (log_div_log_sourceW_tendsto.const_mul 2)).add floorRemainder_tendsto
  convert! hh using 1
  · funext L
    unfold paperGap
    ring
  · ring_nf

theorem rootW_tendsto : Tendsto ErdosInverseBoxHeight.sourceW atTop atTop := by
  exact sourceW_tendsto.comp Real.tendsto_log_atTop

theorem rootB_tendsto : Tendsto ErdosInverseBoxHeight.sourceB atTop atTop := by
  exact sourceB_tendsto.comp Real.tendsto_log_atTop

theorem actual_root_eventually (a : ℝ) : ∀ᶠ z : ℝ in atTop,
    0 < ErdosInverseBoxHeight.sourceB z ∧ 1 < ErdosInverseBoxHeight.sourceW z ∧
    Real.log (ErdosInverseBoxHeight.sourceB z) ≤ 2*Real.log (ErdosInverseBoxHeight.sourceW z) ∧
    199/100 ≤ (sourceRootNode a z).ratio ∧ (sourceRootNode a z).ratio ≤ 23/10 ∧
    0 < (sourceRootNode a z).gap ∧ Consistent (sourceRootNode a z) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (paper_start_eventually a true floorRemainder_tendsto),
    Real.tendsto_log_atTop.eventually source_scale_eventually,eventually_gt_atTop (1:ℝ)] with z hp hs hz
  simp only [sourceRoot_eq_paper a hz hs.1]
  exact hp

theorem actual_root_ratio_tendsto (a : ℝ) :
    Tendsto (fun z => (sourceRootNode a z).ratio) atTop (𝓝 2) := by
  have hh := (paper_ratio_tendsto a floorRemainder_tendsto).comp Real.tendsto_log_atTop
  apply hh.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually source_scale_eventually,eventually_gt_atTop (1:ℝ)] with z hs hz
  rw [sourceRoot_eq_paper a hz hs.1]
  rfl

theorem actual_root_centered_gap_tendsto (a : ℝ) :
    Tendsto (fun z => (sourceRootNode a z).gap-2*ErdosInverseBoxHeight.sourceB z) atTop (𝓝 (-a)) := by
  have hh := (centered_paper_gap_tendsto a).comp Real.tendsto_log_atTop
  apply hh.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually source_scale_eventually,eventually_gt_atTop (1:ℝ)] with z hs hz
  rw [sourceRoot_eq_paper a hz hs.1]
  rfl

end ErdosSourceReferenceMargin

end

end Erdos970

end OAI
