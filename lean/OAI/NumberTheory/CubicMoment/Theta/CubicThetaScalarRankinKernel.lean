import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarHeightCutoff
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarWindow

namespace OAI

/-! The positive truncated scalar kernel on the actual arithmetic quotient.
Its residue is known before any integration against the theta norm. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable
local instance : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
local instance : Countable CubicThetaBottomRow := by
  have hi : Function.Injective (fun r : CubicThetaBottomRow => (r.c,r.d)) := by
    intro r s h
    exact CubicThetaBottomRow.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2
  exact hi.countable

lemma cubicThetaScalarHeightCutoff_nonneg {p : ℂ × ℝ} (hp : 0<p.2) (s : ℝ) :
    0≤cubicThetaScalarHeightCutoff p s := by
  apply tsum_nonneg
  intro r
  split_ifs
  · exact Real.rpow_nonneg (r.height_pos hp).le _
  · exact le_rfl

lemma cubicThetaScalarHeightCutoff_invariant (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℝ) :
    cubicThetaScalarHeightCutoff (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaScalarHeightCutoff p s := by
  unfold cubicThetaScalarHeightCutoff
  simp_rw [←CubicThetaBottomRow.height_rightMul _ g hp]
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq
    (fun r => if r.height p≤1 then r.height p^s else (0:ℝ))

lemma cubicThetaScalarHeightCutoff_point_measurable (s : ℝ) :
    Measurable (fun p : CubicThetaPoint => cubicThetaScalarHeightCutoff p.val s) := by
  apply Measurable.tsum
  intro r
  have hc : Continuous (fun p : CubicThetaPoint => r.height p.val) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (r.height_contDiffAt p.property).continuousAt.comp
      continuous_subtype_val.continuousAt
  apply Measurable.ite (measurableSet_le hc.measurable measurable_const)
  · exact (hc.rpow_const (fun p => Or.inl (r.height_pos p.property).ne')).measurable
  · exact measurable_const

def cubicThetaScalarRankinKernel (σ : ℝ) (q : CubicThetaQuotient) : ℝ :=
  cubicThetaScalarHeightCutoff (cubicThetaBorelSection q).val (2+2*σ)

lemma cubicThetaScalarRankinKernel_measurable (σ : ℝ) :
    Measurable (cubicThetaScalarRankinKernel σ) :=
  (cubicThetaScalarHeightCutoff_point_measurable _).comp cubicThetaBorelSection_measurable

lemma cubicThetaScalarRankinKernel_nonneg (σ : ℝ) (q : CubicThetaQuotient) :
    0≤cubicThetaScalarRankinKernel σ q :=
  cubicThetaScalarHeightCutoff_nonneg (cubicThetaBorelSection q).property _

theorem cubicThetaScalarRankinKernel_residue (q : CubicThetaQuotient) :
    Tendsto (fun σ : ℝ => (σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ))
      (𝓝[>] 0) (𝓝 ((Real.pi:ℂ)^2/(108*principalIdealZeta 2))) := by
  have hpath : Tendsto (fun σ : ℝ => 2+2*σ) (𝓝[>] 0) (𝓝[>] 2) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : ContinuousAt (fun σ : ℝ => 2+2*σ) 0 := by fun_prop
      simpa using h.tendsto.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      change 0<σ at hσ
      change 2<2+2*σ
      linarith
  have h := ((cubicThetaScalarHeightCutoff_residue (cubicThetaBorelSection q).property).comp hpath).const_mul (1/2:ℂ)
  convert h using 1
  · funext σ
    dsimp only [Function.comp_apply,cubicThetaScalarRankinKernel]
    push_cast
    ring
  · congr 1
    ring

end CubicFirstMoment

end

end OAI
