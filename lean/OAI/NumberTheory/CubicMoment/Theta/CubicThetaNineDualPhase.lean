import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCommonCuspCoefficient

namespace OAI

/-! A lower-right entry divisible by nine identifies the actual dual
phase with an ordinary residue-ring additive character. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicTheta_additivePhase_one (a : Eisenstein) : additivePhase 1 a=1 := by
  rw [additivePhase_congr one_ne_zero (residue_eq_of_dvd_sub (one_dvd (a-0))),additivePhase_zero]

lemma cubicTheta_trace_integral_phase (a : Eisenstein) :
    (Real.fourierChar (tracePair (a:ℂ) 1):ℂ)=1 := by
  simpa only [additivePhase_fourierChar,Subalgebra.coe_one,div_one] using cubicTheta_additivePhase_one a

lemma cubicThetaNineDual_phase (g : SL(2,Eisenstein)) (r δ : Eisenstein)
    (hc : g 1 0=r) (hd : g 1 1=9*δ) (n : Eisenstein) :
    (Real.fourierChar (tracePair (cubicThetaFrequency n) (cubicThetaPrimaryDualCenter g)):ℂ)=
      additivePhase r (-n*δ) := by
  have he : tracePair (cubicThetaFrequency n) (cubicThetaPrimaryDualCenter g)=
      tracePair ((n*δ:Eisenstein):ℂ) 1+
        tracePair ((-n*δ:Eisenstein):ℂ) (1/(r:ℂ)) := by
    rw [cubicThetaFrequency_div_nine]
    unfold cubicThetaPrimaryDualCenter
    rw [hc,hd]
    unfold tracePair
    push_cast
    simp only [mul_one,one_div]
    rw [←mul_add,←Complex.add_re]
    rw [show ((9:Eisenstein):ℂ)=(9:ℂ) from rfl]
    congr 2
    ring
  rw [he,AddChar.map_add_eq_mul,Circle.coe_mul,cubicTheta_trace_integral_phase,one_mul]
  exact (additivePhase_fourierChar _ _).symm

lemma cubicThetaNineGaussMatrix_weighted_coefficient (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) (δ : Eisenstein)
    (hd : cubicThetaNineGaussMatrix r hr u hu 1 1=9*δ) (n : Eisenstein) :
    cubicSymbol r u*cubicThetaCoefficientTwist
      (cubicThetaProjectedCoefficient (cubicThetaNineGaussMatrix r hr u hu)
        (cubicThetaNineGaussMatrix_primary r hr u hu))
      (cubicThetaPrimaryDualCenter (cubicThetaNineGaussMatrix r hr u hu)) n=
      cubicThetaCommonCuspCoefficient n*additivePhase r (-n*δ) := by
  rw [cubicThetaCoefficientTwist,cubicThetaNineGaussMatrix_coefficient,
    cubicThetaNineDual_phase _ r δ (cubicThetaNineGaussMatrix_entries r hr u hu).2.1 hd]
  have he : cubicSymbol r u*star (cubicSymbol r u)=1 := by
    rw [Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hr hu]
    norm_num
  calc
    _ = (cubicSymbol r u*star (cubicSymbol r u))*
      (cubicThetaCommonCuspCoefficient n*additivePhase r (-n*δ)) := by ring
    _ = _ := by rw [he,one_mul]

lemma cubicThetaNineGaussMatrix_inverse (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) (δ : Eisenstein)
    (hd : cubicThetaNineGaussMatrix r hr u hu 1 1=9*δ) :
    r∣(9*lambdaE^3*u*δ)-1 := by
  let g := cubicThetaNineGaussMatrix r hr u hu
  have he : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  rw [(cubicThetaNineGaussMatrix_entries r hr u hu).1,
    (cubicThetaNineGaussMatrix_entries r hr u hu).2.1,hd] at he
  refine ⟨g 0 1,?_⟩
  linear_combination he

end CubicFirstMoment

end

end OAI
