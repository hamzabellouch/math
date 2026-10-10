import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticModelL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoefficientScalar

namespace OAI

/-! Weighted Fourier observations identify the arithmetic residue with
the explicit coefficient model, retaining its one actual base scalar. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaArithmeticModel_horizontal (A : ℂ) {v : ℝ} (hv : 0<v)
    (h : Eisenstein) :
    (∫ z in cubicThetaHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
        cubicThetaArithmeticModel A (z,v))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*
        (if h=0 then ((cubicThetaConstant*v^(2/3:ℝ):ℝ):ℂ)
        else A*cubicThetaArithmeticCoefficient (-lambdaE*h)*
          cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v)) := by
  rw [cubicThetaHorizontalCoefficient (fun z => cubicThetaArithmeticModel A (z,v))
    (cubicThetaArithmeticModelTorus A v) h
    (fun x => (cubicThetaArithmeticModelTorus_real A hv x).symm),
    cubicThetaArithmeticModelTorus_coefficient A hv]
  rfl

lemma cubicThetaArithmeticModel_pair_integrable (A : ℂ) (h : Eisenstein) (W : C_c(ℝ,ℂ)) :
    IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
        cubicThetaArithmeticModel A p.val) (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hi := L2.integrable_inner (𝕜:=ℂ) (cubicThetaCuspFourierTest h W)
    (cubicThetaArithmeticModelStrip A)
  apply hi.congr
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
    (cubicThetaArithmeticModel_memLp A).coeFn_toLp] with p hW hF
  change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p)
    (((cubicThetaArithmeticModel_memLp A).toLp _) p)=_
  rw [hW,hF,RCLike.inner_apply]
  simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
  ring

lemma cubicThetaArithmeticModel_observation (A : ℂ) (h : Eisenstein) (W : C_c(ℝ,ℂ)) :
    inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaArithmeticModelStrip A)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*
        ∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*
          (if h=0 then ((cubicThetaConstant*v^(2/3:ℝ):ℝ):ℂ)
          else A*cubicThetaArithmeticCoefficient (-lambdaE*h)*
            cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v)) := by
  have hp : inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaArithmeticModelStrip A)=
      ∫ p in cubicThetaCuspStrip 2,
        star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
          cubicThetaArithmeticModel A p.val ∂cubicThetaPointMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
      (cubicThetaArithmeticModel_memLp A).coeFn_toLp] with p hW hF
    change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p)
      (((cubicThetaArithmeticModel_memLp A).toLp _) p)=_
    rw [hW,hF,RCLike.inner_apply]
    simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
    ring
  have he := cubicThetaCuspStrip_fubini
    (fun y => star (W y.2*(Real.fourierChar (tracePair y.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaArithmeticModel A y) (cubicThetaArithmeticModel_pair_integrable A h W)
  change (∫ p in cubicThetaCuspStrip 2,
    star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaArithmeticModel A p.val ∂cubicThetaPointMeasure)=_ at he
  rw [hp,he,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  change 2<v at hv
  have he := cubicThetaArithmeticModel_horizontal A (show 0<v by linarith) h
  calc
    _ = star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
            cubicThetaArithmeticModel A (z,v) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
      intro z _
      simp only [star_mul]
      ring
    _ = _ := by rw [he]; ring

theorem cubicThetaArithmeticModel_nonzero_observation {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) :
    inner ℂ (cubicThetaCuspFourierTest h W)
      (cubicThetaCuspRestriction cubicThetaNormalizedArithmeticResidue)=
    inner ℂ (cubicThetaCuspFourierTest h W)
      (cubicThetaArithmeticModelStrip cubicThetaArithmeticBaseScalar) := by
  rw [cubicThetaNormalizedArithmeticResidue_observation hh,
    cubicThetaCoefficientScalar hh,cubicThetaArithmeticModel_observation]
  simp only [ite_eq_right hh]
  rw [mul_assoc]
  congr 1
  rw [←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  ring

theorem cubicThetaArithmeticModel_zero_observation (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) :
    inner ℂ (cubicThetaCuspFourierTest 0 W)
      (cubicThetaCuspRestriction cubicThetaNormalizedArithmeticResidue)=
    inner ℂ (cubicThetaCuspFourierTest 0 W)
      (cubicThetaArithmeticModelStrip cubicThetaArithmeticBaseScalar) := by
  rw [cubicThetaNormalizedArithmeticResidue_constant W hW,
    cubicThetaArithmeticModel_observation]
  simp only [ite_true]
  rw [mul_assoc]
  congr 1
  unfold cubicThetaZeroRadialTest
  rw [←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  change 2<v at hv
  have hc : ((v^(2/3:ℝ):ℝ):ℂ)=(v:ℂ)^(2/3:ℂ) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using
      Complex.ofReal_cpow (show 0≤v by linarith) (2/3:ℝ)
  have hp : (2:ℂ)-(4/3:ℂ)=(2/3:ℂ) := by norm_num
  rw [hp,Complex.ofReal_mul,hc]
  ring

theorem cubicThetaArithmeticModel_all_observations (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) :
    inner ℂ (cubicThetaCuspFourierTest h W)
      (cubicThetaCuspRestriction cubicThetaNormalizedArithmeticResidue)=
    inner ℂ (cubicThetaCuspFourierTest h W)
      (cubicThetaArithmeticModelStrip cubicThetaArithmeticBaseScalar) := by
  by_cases hh : h=0
  · subst h
    exact cubicThetaArithmeticModel_zero_observation W hW
  · exact cubicThetaArithmeticModel_nonzero_observation hh W

end CubicFirstMoment

end

end OAI
