import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoefficientScalar

namespace OAI

/-! Exact squared sizes of the theta coefficients, for normalization by
their Fourier energy. The zero classes remain in the formula. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaTwistedGauss_unit_lambda_norm {c : Eisenstein} (hc : primary c)
    (hs : Squarefree c) (u : Eisensteinˣ) :
    ‖cubicThetaTwistedGauss c ((u:Eisenstein)^4*lambdaE^2)‖=1 := by
  have hu : IsCoprime c ((u:Eisenstein)^4) := by
    refine ⟨0,(↑(u⁻¹):Eisenstein)^4,?_⟩
    simp only [zero_mul,zero_add,←mul_pow]
    simp
  have hcop : IsCoprime c ((u:Eisenstein)^4*lambdaE^2) :=
    hu.mul_right (primary_coprime_lambda hc).pow_right
  rw [cubicThetaTwistedGauss,norm_mul,norm_star,
    norm_cubicSymbol_of_isCoprime hc hcop,norm_gauss_of_squarefree hc hs,one_mul]

lemma CubicThetaCoordinates.coefficient_norm {n : Eisenstein} (R : CubicThetaCoordinates n) :
    ‖R.coefficient‖=
      if R.order%3=0 ∧ 3≤R.order then R.amplitude
      else if R.order%3=1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)=-1)
        then R.amplitude else 0 := by
  classical
  unfold coefficient
  split_ifs
  · rw [norm_mul,norm_mul,norm_star,cubicThetaUnitPhase_norm,
      cubicThetaTwistedGauss_unit_lambda_norm R.squarefree_primary R.squarefree,
      mul_one,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
  · rw [norm_mul,norm_star,norm_gauss_of_squarefree R.squarefree_primary R.squarefree,
      mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
  · exact norm_zero

lemma CubicThetaCoordinates.amplitude_sq {n : Eisenstein} (R : CubicThetaCoordinates n) :
    R.amplitude^2=
      3^(8-2*((R.order/3:ℕ):ℝ))/(norm R.squarefreePart*(norm R.cubePart)^2) := by
  unfold amplitude
  rw [div_pow,mul_pow,Real.sq_sqrt (norm_nonneg _),
    ←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
  congr 2
  push_cast
  ring

theorem cubicThetaNormalizedCoefficient_energy {n : Eisenstein}
    (R : CubicThetaCoordinates (-lambdaE*n)) (hn : n≠0) :
    ‖cubicThetaNormalizedObservedCoefficient n‖^2=
      ‖cubicThetaArithmeticBaseScalar‖^2*‖R.coefficient‖^2 := by
  rw [cubicThetaCoefficientScalar hn,cubicThetaArithmeticCoefficient_formula R,norm_mul,mul_pow]

end CubicFirstMoment

end

end OAI
