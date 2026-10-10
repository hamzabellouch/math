import OAI.Geometry.NodalSets.Elliptic.SeedPolynomialDerivatives

namespace OAI

namespace Yau.Target
noncomputable section

lemma seedQuadraticDerivative_radial (x : SeedAmbient) :
    seedQuadraticDerivative x x = 2 * seedQuadratic x := by
  simp only [seedQuadraticDerivative,add_apply,smul_apply,smul_eq_mul,seedQuadratic]
  ring

lemma ambientComplexSeed_radial (N : ℕ) (x : SeedAmbient) :
    fderiv ℝ (ambientComplexSeed N) x x = (2*(N:ℂ))*ambientComplexSeed N x := by
  rw [ambientComplexSeed_fderiv]
  change (N:ℂ) * seedQuadratic x^(N-1) * seedQuadraticDerivative x x = _
  rw [seedQuadraticDerivative_radial]
  simp only [ambientComplexSeed]
  cases N with
  | zero => simp
  | succ n => simp only [Nat.succ_sub_one,Nat.cast_succ,pow_succ]; ring

lemma ambientComplexSeed_second_radial (N : ℕ) (x : SeedAmbient) :
    fderiv ℝ (fun y ↦ fderiv ℝ (ambientComplexSeed N) y x) x x =
      (2*(N:ℂ))*(2*(N:ℂ)-1)*ambientComplexSeed N x := by
  rw [ambientComplexSeed_second,seedQuadraticDerivative_radial]
  rw [show seedZ2 x * seedZ1 x + seedZ1 x * seedZ2 x = 2*seedQuadratic x by
    unfold seedQuadratic; ring]
  simp only [ambientComplexSeed]
  rcases N with _ | (_ | n)
  · simp
  · norm_num
  · simp only [Nat.succ_sub_one,Nat.cast_succ,pow_succ]; ring

lemma ambientRealSeed_radial (N : ℕ) (x : SeedAmbient) :
    fderiv ℝ (ambientRealSeed N) x x = (2*(N:ℝ))*ambientRealSeed N x := by
  rw [ambientRealSeed_fderiv,ambientComplexSeed_radial]
  simp [ambientRealSeed,Complex.mul_re]

lemma ambientRealSeed_second_radial (N : ℕ) (x : SeedAmbient) :
    fderiv ℝ (fun y ↦ fderiv ℝ (ambientRealSeed N) y x) x x =
      (2*(N:ℝ))*(2*(N:ℝ)-1)*ambientRealSeed N x := by
  rw [ambientRealSeed_second,ambientComplexSeed_second_radial]
  simp [ambientRealSeed,Complex.mul_re]

end
end Yau.Target

end OAI
