import OAI.NumberTheory.Jacobsthal.Estimates.CorrectionFloorRemainder

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly ErdosBoundaryIntegral
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.PrimeBinMembership NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.JacobsthalSourceScale
open Erdos970Dependency.InvariantCostBound

noncomputable def paperStart (a : ℝ) (e : ℝ → ℝ) (closed : Bool) (L : ℝ) : Node where
  side := .even
  gap := paperGap a e L
  ratio := paperGap a e L/sourceB L
  cutoff := sourceB L
  closed := closed

theorem paper_start_eventually (a : ℝ) (closed : Bool) {e : ℝ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    ∀ᶠ L : ℝ in atTop,
      0 < sourceB L ∧ 1 < sourceW L ∧
      Real.log (sourceB L) ≤ 2*Real.log (sourceW L) ∧
      199/100 ≤ (paperStart a e closed L).ratio ∧ (paperStart a e closed L).ratio ≤ 23/10 ∧
      0 < (paperStart a e closed L).gap ∧ Consistent (paperStart a e closed L) := by
  have hr := (paper_ratio_tendsto a he).eventually
    (Ioo_mem_nhds (by norm_num : (199:ℝ)/100 < 2) (by norm_num : (2:ℝ) < 23/10))
  filter_upwards [source_scale_eventually,hr] with L hs hr
  have hB : 0 < sourceB L := hs.2.1
  have hg : 0 < paperGap a e L := by
    have hh := (lt_div_iff₀ hB).mp hr.1
    nlinarith
  refine ⟨hB,hs.1,hs.2.2.2.2,hr.1.le,hr.2.le,hg,?_⟩
  change sourceB L=paperGap a e L/(paperGap a e L/sourceB L)
  field_simp

theorem paper_normalized_correction_tendsto (a : ℝ) (closed : Bool) {e : ℝ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun L => ((paperStart a e closed L).gap^2/weight .even (paperStart a e closed L).ratio)*
      continuousBoundaryCorrection (sourceW L) 2 (paperStart a e closed L)) atTop
      (𝓝 (2*signedCoefficientI/costMass)) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨B₀,w₀,_hB₀,_hw₀,h⟩ := full_continuous_correction_limit 2 (eps/2) (by norm_num) (by linarith)
  filter_upwards [paper_start_eventually a closed he,
    sourceB_tendsto.eventually (eventually_ge_atTop B₀),
    sourceW_tendsto.eventually (eventually_ge_atTop w₀)] with L hs hB hw
  have hh := h (sourceB L) (sourceW L) hB hw hs.2.2.1
    (paperStart a e closed L) rfl hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.2 rfl
  rw [Real.dist_eq]
  exact hh.trans_lt (by linarith)

theorem paper_continuous_correction_tendsto (a : ℝ) (closed : Bool) {e : ℝ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun L => (sourceB L)^2*continuousBoundaryCorrection (sourceW L) 2 (paperStart a e closed L))
      atTop (𝓝 (Real.exp Real.eulerMascheroniConstant*(2*signedCoefficientI/costMass))) := by
  have ht := (paper_prefactor_tendsto a he).mul (paper_normalized_correction_tendsto a closed he)
  apply ht.congr'
  filter_upwards [paper_start_eventually a closed he] with L hs
  have hg : paperGap a e L ≠ 0 := hs.2.2.2.2.2.1.ne'
  have hp : phiEven (paperGap a e L/sourceB L) ≠ 0 :=
    (phiEven_pos (by have hh := hs.2.2.2.1; change 199/100 ≤ paperGap a e L/sourceB L at hh; linarith)).ne'
  change (sourceB L)^2*phiEven (paperGap a e L/sourceB L)/(paperGap a e L)^2*
    ((paperGap a e L)^2/phiEven (paperGap a e L/sourceB L)*
      continuousBoundaryCorrection (sourceW L) 2 (paperStart a e closed L))=_
  field_simp

theorem paper_z_continuous_correction_tendsto (a : ℝ) (closed : Bool) {e : ℝ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun z => (sourceB (Real.log z))^2*
      continuousBoundaryCorrection (sourceW (Real.log z)) 2 (paperStart a e closed (Real.log z))) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant*(2*signedCoefficientI/costMass))) := by
  exact (paper_continuous_correction_tendsto a closed he).comp Real.tendsto_log_atTop

end ErdosCorrectionLimit

end

end Erdos970

end OAI
