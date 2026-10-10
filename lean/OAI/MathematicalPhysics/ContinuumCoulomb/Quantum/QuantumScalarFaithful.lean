import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAlgebraicScalar
import Mathlib.NumberTheory.Real.Irrational

namespace OAI

/-! The four rational registers faithfully represent their complex value.
This permits exact local-table identities to reuse the established complex
matrix identities, without changing the arithmetic program. -/

namespace ContinuumCoulomb.QuantumAlgebraicScalar

theorem sqrtHalf_irrational : Irrational (Real.sqrt (1/2 : ℝ)) := by
  rw [Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one,one_div]
  exact irrational_sqrt_two.inv

theorem realValue_injective : Function.Injective realValue := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hb : b=d := by
    by_contra hbd
    have hi := (sqrtHalf_irrational.ratCast_mul (sub_ne_zero.mpr hbd)).ratCast_add (a-c)
    have hz : ((a-c : ℚ) : ℝ)+((b-d : ℚ) : ℝ)*Real.sqrt (1/2 : ℝ)=0 := by
      dsimp only [realValue] at h
      push_cast
      nlinarith [h]
    rw [hz] at hi
    exact not_irrational_zero hi
  have ha : a=c := by
    subst d
    have he : (a:ℝ)=(c:ℝ) := by
      dsimp only [realValue] at h
      linarith
    exact_mod_cast he
  exact Prod.ext ha hb

theorem value_injective : Function.Injective value := by
  intro x y h
  apply Prod.ext
  · apply realValue_injective
    simpa only [value_re] using congrArg Complex.re h
  · apply realValue_injective
    simpa only [value_im] using congrArg Complex.im h

theorem scalar_eq_iff (x y : Scalar) : x=y ↔ value x=value y :=
  ⟨congrArg value,fun h => value_injective h⟩

end ContinuumCoulomb.QuantumAlgebraicScalar

end OAI
