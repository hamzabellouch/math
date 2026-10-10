import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveCuspRestriction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticModelL2

namespace OAI

/-! The literal arithmetic series in the L2 space of every positive
height strip, with its scalar still retained. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaArithmeticModel_point_continuous (A : ℂ) :
    Continuous (fun p : CubicThetaPoint => cubicThetaArithmeticModel A p.val) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hc : ContinuousAt (cubicThetaArithmeticModel A) p.val := by
    unfold cubicThetaArithmeticModel
    apply ContinuousAt.add
    · apply Complex.continuous_ofReal.continuousAt.comp
      exact (continuousAt_snd.rpow_const (Or.inl p.property.ne')).const_mul _
    · exact (cubicThetaNonconstant_continuousAt (by norm_num : (0:ℝ)≤81)
        cubicThetaArithmeticCoefficient_bound p.property).const_mul A
  exact hc.comp continuous_subtype_val.continuousAt

lemma cubicThetaArithmeticModel_positive_memLp (A : ℂ) {ε : ℝ} (hε : 0<ε) :
    MemLp (fun p : CubicThetaPoint => cubicThetaArithmeticModel A p.val) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)) := by
  obtain ⟨K,hK,hcover⟩ := cubicThetaPositiveStrip_compact_cover hε
  have hc := cubicThetaArithmeticModel_point_continuous A
  have hlow : IntegrableOn (fun p : CubicThetaPoint =>
      ‖cubicThetaArithmeticModel A p.val‖^2) K cubicThetaPointMeasure :=
    (hc.norm.pow 2).continuousOn.integrableOn_compact hK
  have hhigh := (cubicThetaArithmeticModel_memLp A).integrable_norm_pow (by norm_num)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  exact (hlow.union hhigh).mono_set hcover

def cubicThetaPositiveModelStrip (A : ℂ) {ε : ℝ} (hε : 0<ε) :
    CubicThetaPositiveStripL2 ε :=
  (cubicThetaArithmeticModel_positive_memLp A hε).toLp _

lemma cubicThetaPositiveFourierWeight_memLp {ε : ℝ} (hε : 0<ε)
    (h : Eisenstein) (W : CompactlySupportedContinuousMap ℝ ℂ) :
    MemLp (cubicThetaCuspFourierWeight h W) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)) := by
  have := cubicThetaPositiveStrip_finite hε
  obtain ⟨C,hC⟩ := W.hasCompactSupport.exists_bound_of_continuousOn W.continuous.continuousOn
  apply MemLp.of_bound (cubicThetaCuspFourierWeight_continuous h W).aestronglyMeasurable (max C 0)
  apply Filter.Eventually.of_forall
  intro p
  rw [cubicThetaCuspFourierWeight,norm_mul,Circle.norm_coe,mul_one]
  by_cases hp : p.val.2∈tsupport W
  · exact (hC p.val.2 hp).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hp,norm_zero]
    exact le_max_right _ _

def cubicThetaPositiveStripFourierTest {ε : ℝ} (hε : 0<ε)
    (h : Eisenstein) (W : CompactlySupportedContinuousMap ℝ ℂ) :
    CubicThetaPositiveStripL2 ε :=
  (cubicThetaPositiveFourierWeight_memLp hε h W).toLp _

end CubicFirstMoment

end

end OAI
