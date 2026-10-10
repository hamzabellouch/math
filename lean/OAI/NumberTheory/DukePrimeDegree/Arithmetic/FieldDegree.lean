import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic

namespace OAI

/-!
# Prime degree excludes quadratic subfields

The tower-degree formula excludes the quadratic subfields in Stark's
exceptional-zero alternative, giving the field-degree hypothesis for
the uniform residue estimate.
-/

namespace DukePrimeDegree

/-- A number field of prime degree at least three has no quadratic
intermediate field over the rationals. -/
theorem no_quadratic_intermediateField
    {K : Type*} [Field K] [NumberField K]
    (hprime : (Module.finrank ℚ K).Prime) (hdegree : 3 ≤ Module.finrank ℚ K)
    (F : IntermediateField ℚ K) : Module.finrank ℚ F ≠ 2 := by
  intro hquadratic
  have hdiv : Module.finrank ℚ F ∣ Module.finrank ℚ K :=
    Module.finrank_dvd_finrank_right ℚ F K
  rw [hquadratic] at hdiv
  rcases (Nat.dvd_prime hprime).mp hdiv with h | h
  · norm_num at h
  · omega

end DukePrimeDegree

end OAI
