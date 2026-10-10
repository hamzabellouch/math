import OAI.MeasureTheory.Falconer.Angular.AngularStripIntervals
import OAI.MeasureTheory.Falconer.Angular.ActualAngularTests
import OAI.MeasureTheory.Falconer.Radial.RadialTestNorm
import Mathlib.Analysis.Complex.Arg

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem planeDot_sourceDirection_complex (z : ℂ) (θ : ℝ) :
    planeDot (Complex.orthonormalBasisOneI.repr z) (sourceDirection θ) =
      ‖z‖*Real.cos (θ-Complex.arg z) := by
  simp only [planeDot,sourceDirection,Complex.orthonormalBasisOneI_repr_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,Complex.add_im,Complex.mul_im,mul_zero,
    sub_zero,add_zero,zero_add,mul_one]
  rw [Real.cos_sub]
  have hc := Complex.norm_mul_cos_arg z
  have hs := Complex.norm_mul_sin_arg z
  rw [← hc,← hs]
  ring

theorem measurableSet_directionStrip (z : Plane) (W : ℝ) :
    MeasurableSet {ω : UnitCircle | |planeDot z (ω:Plane)| ≤ W} := by
  apply measurableSet_le _ measurable_const
  have hc : Continuous (fun ω : UnitCircle => |planeDot z (ω:Plane)|) := by
    unfold planeDot
    fun_prop
  exact hc.measurable

theorem sourceArcLength_strip_linear (z : Plane) (hz : z ≠ 0) {W : ℝ} (hW : 0 ≤ W) :
    sourceArcLength {ω : UnitCircle | |planeDot z (ω:Plane)| ≤ W} ≤
      ENNReal.ofReal (4*Real.pi*(W/‖z‖)) := by
  let c := Complex.orthonormalBasisOneI.repr.symm z
  have hc : Complex.orthonormalBasisOneI.repr c = z := by exact Complex.orthonormalBasisOneI.repr.apply_symm_apply z
  have hn : ‖c‖ = ‖z‖ := Complex.orthonormalBasisOneI.repr.symm.norm_map z
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have he (θ : ℝ) : |planeDot z (sourceDirection θ)| ≤ W ↔
      |Real.cos (θ-Complex.arg c)| ≤ W/‖z‖ := by
    rw [← hc,planeDot_sourceDirection_complex,abs_mul,abs_of_nonneg (norm_nonneg c),hn,hc]
    simpa only [mul_comm] using (le_div_iff₀ (a := |Real.cos (θ-Complex.arg c)|) (b := W) hp).symm
  rw [sourceArcLength,Measure.map_apply continuous_sourceUnitDirection.measurable
    (measurableSet_directionStrip z W),Measure.restrict_apply
    ((measurableSet_directionStrip z W).preimage continuous_sourceUnitDirection.measurable)]
  have hset : sourceUnitDirection ⁻¹' {ω : UnitCircle | |planeDot z (ω:Plane)| ≤ W} ∩
      Ioc 0 (2*Real.pi) =
      {θ : ℝ | θ ∈ Ioc 0 (2*Real.pi) ∧ |Real.cos (θ-Complex.arg c)| ≤ W/‖z‖} := by
    ext θ
    simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq,sourceUnitDirection,he]
    exact and_comm
  rw [hset]
  exact volume_cos_strip ⟨(Complex.neg_pi_lt_arg c).le,Complex.arg_le_pi c⟩
    (div_nonneg hW hp.le)

theorem sourceArcLength_univ : sourceArcLength univ = ENNReal.ofReal (2*Real.pi) := by
  rw [sourceArcLength,Measure.map_apply continuous_sourceUnitDirection.measurable MeasurableSet.univ]
  simp

theorem sourceArcLength_strip (z : Plane) (hz : z ≠ 0) {W : ℝ} (hW : 0 ≤ W) :
    sourceArcLength {ω : UnitCircle | |planeDot z (ω:Plane)| ≤ W} ≤
      ENNReal.ofReal (4*Real.pi*min 1 (W/‖z‖)) := by
  by_cases h : W/‖z‖ ≤ 1
  · rw [min_eq_right h]
    exact sourceArcLength_strip_linear z hz hW
  · rw [min_eq_left (le_of_not_ge h)]
    calc
      _ ≤ sourceArcLength univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal (2*Real.pi) := sourceArcLength_univ
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos])

end PlanarFalconer

end OAI
