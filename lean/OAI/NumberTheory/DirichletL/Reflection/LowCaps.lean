import OAI.NumberTheory.DirichletL.Reflection.LowWidth
import OAI.NumberTheory.DirichletL.Reflection.ActualSizeCaps

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma low_actual_scale_caps (J I Q Q₀ : Ideal Eis) (hJ : J≠0) (hI : I≠0) (hQ : Q≠0)
    (hpower : rowPowerfulPart J=rowPowerfulPart I) (hmask : rowMaskPart J Q=rowMaskPart I Q)
    (A : Finset (FreeReflection.pool J Q Q₀))
    (Z Ck d ell0 shift η QK QP : ℝ) (hZ : 2≤Z) (hCkp : 0<Ck) (hCk : Ck≤Z)
    (hQn : (Ideal.absNorm Q:ℝ)≤Z) (hd : 0≤d) (hell : 0≤ell0)
    (hellcap : ell0≤1/6-d+η) (hshift : |shift|≤η) (hη : η≤1)
    (hIn : (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d))
    (hK : QK≤2*Ck*Z^(5/6-2*d)) (hP : QP/2≤Z^ell0) :
    (Ideal.absNorm I:ℝ)≤Z^2 ∧
    (Ideal.absNorm (∏ b : A,((poolPrimeFamily J Q Q₀).restrict A).ideal b):ℝ)≤Z^(8:ℝ) ∧
      QK≤Z^(8:ℝ) ∧ QP≤Z^(8:ℝ) ∧ (Z^(1+ell0+shift))⁻¹≤Z^(8:ℝ) := by
  have hz : 0<Z := by linarith
  have hz1 : 1≤Z := by linarith
  have hcp : Ck*Z^(5/6-2*d)≤Z^2 := by
    calc
      _ ≤ Z*Z^(5/6-2*d) := mul_le_mul_of_nonneg_right hCk (Real.rpow_nonneg hz.le _)
      _ = Z^(1+(5/6-2*d)) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ _ := by
        rw [←Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
  have hi := hIn.trans hcp
  refine ⟨hi,?_,?_,?_,?_⟩
  · calc
      _ ≤ (Ideal.absNorm I:ℝ)*(Ideal.absNorm Q:ℝ) := original_pool_restricted_norm J I Q Q₀ hJ hI hQ hpower hmask A
      _ ≤ Z^2*Z := mul_le_mul hi hQn (Nat.cast_nonneg _) (sq_nonneg _)
      _ = Z^(3:ℝ) := by norm_num;ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
  · calc
      QK ≤ 2*(Ck*Z^(5/6-2*d)) := by linarith
      _ ≤ Z*Z^2 := mul_le_mul hZ hcp (by positivity) hz.le
      _ = Z^(3:ℝ) := by norm_num;ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
  · calc
      QP ≤ 2*Z^ell0 := by linarith
      _ ≤ Z*Z^ell0 := mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hz.le _)
      _ = Z^(1+ell0) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
  · rw [←Real.rpow_neg hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hz1 (by have hs := (abs_le.mp hshift).1;linarith)

lemma low_reflection_parameters (η : ℝ) (hη : 0<η) :
    0<η/(200*(1+η)) ∧
    η/(200*(1+η))*(8+8+2*(η/2+57+η))+η/2≤2*η := by
  have hp : 0<200*(1+η) := by positivity
  constructor
  · positivity
  · apply (mul_le_mul_iff_left₀ hp).mp
    field_simp
    nlinarith [sq_nonneg η]
end
end SevenEighths.InverseReflectedPhase

end OAI
