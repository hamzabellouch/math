import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspObservable
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaStripFiniteVolume
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierCoefficients

namespace OAI

/-! Genuine weighted Fourier observations on the high arithmetic cusp.
They are bounded L2 functionals of the actual meromorphic continuation. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaCuspFourierWeight (h : Eisenstein) (W : C_c(ℝ,ℂ)) (p : CubicThetaPoint) : ℂ :=
  W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ)

lemma cubicThetaCuspFourierWeight_continuous (h : Eisenstein) (W : C_c(ℝ,ℂ)) :
    Continuous (cubicThetaCuspFourierWeight h W) := by
  have hc : Continuous (fun p : CubicThetaPoint =>
      Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h))) :=
    Real.continuous_fourierChar.comp (by unfold tracePair; fun_prop)
  exact (W.continuous.comp (continuous_snd.comp continuous_subtype_val)).mul
    (continuous_subtype_val.comp hc)

lemma cubicThetaCuspFourierWeight_memLp (h : Eisenstein) (W : C_c(ℝ,ℂ)) :
    MemLp (cubicThetaCuspFourierWeight h W) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
  obtain ⟨C,hC⟩ := W.hasCompactSupport.exists_bound_of_continuousOn W.continuous.continuousOn
  apply MemLp.of_bound (cubicThetaCuspFourierWeight_continuous h W).aestronglyMeasurable (max C 0)
  apply Filter.Eventually.of_forall
  intro p
  rw [cubicThetaCuspFourierWeight,norm_mul,Circle.norm_coe,mul_one]
  by_cases hp : p.val.2∈tsupport W
  · exact (hC p.val.2 hp).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hp,norm_zero]
    exact le_max_right _ _

def cubicThetaCuspFourierTest (h : Eisenstein) (W : C_c(ℝ,ℂ)) : CubicThetaStripL2 :=
  (cubicThetaCuspFourierWeight_memLp h W).toLp _

def cubicThetaCuspFourierObservable (h : Eisenstein) (W : C_c(ℝ,ℂ)) (s : ℂ) : ℂ :=
  cubicThetaCuspObservable (cubicThetaCuspFourierTest h W) s

theorem cubicThetaCuspFourierObservable_meromorphic (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 1<s.re) : MeromorphicAt (cubicThetaCuspFourierObservable h W) s :=
  cubicThetaCuspObservable_meromorphic _ hs

lemma cubicThetaCuspFourierObservable_right (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 3<s.re) :
    cubicThetaCuspFourierObservable h W s=
      ∫ p in cubicThetaCuspStrip 2,
        star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
          cubicThetaArithmeticRemainder p.val s ∂cubicThetaPointMeasure := by
  rw [cubicThetaCuspFourierObservable,cubicThetaCuspObservable_right _ hs]
  apply integral_congr_ae
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp] with p hp
  change star (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p)*_=_
  rw [hp]
  rfl

end CubicFirstMoment

end

end OAI
