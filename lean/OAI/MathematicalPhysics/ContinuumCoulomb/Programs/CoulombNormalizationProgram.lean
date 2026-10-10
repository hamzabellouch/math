import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombNormalizationError

namespace OAI

/-! A certified rational evaluator for the fixed Coulomb normalization
factor. The natural guard depends only on the fixed one-well model. -/

noncomputable section
namespace ContinuumCoulomb.CoulombNormalization
open ExactQuantumFactoring.BitStackProgram

def guard (freq : ℝ) : ℕ := Nat.ceil (max 1 (max |freq|
  (max (2 / (∫ r, planarResolventMode r ^ 2)) (2 / Real.pi)))) + 1

def coefficient (freq : ℝ) : ℝ := freq / ((∫ r, planarResolventMode r ^ 2) ^ 2 * Real.pi)
def factorBound (C : ℕ) : ℕ := C ^ 3 + 3 * C ^ 5
def precision (rho P : ℕ) : ℕ :=
  (guard (GaussianFrequency.frequency rho) + factorBound (guard (GaussianFrequency.frequency rho))) * (P + 1)

def approximate (rho P : ℕ) : ℚ :=
  GaussianFrequency.approximate rho (precision rho P) /
    (NormalizationSchedule.approximate (precision rho P) ^ 2 *
      PiProgram.approximate (8 * (precision rho P + 1)))

theorem guard_bounds (freq : ℝ) :
    1 ≤ (guard freq : ℝ) ∧ |freq| ≤ (guard freq : ℝ) ∧
      2 ≤ (guard freq : ℝ) * (∫ r, planarResolventMode r ^ 2) ∧
      2 ≤ (guard freq : ℝ) * Real.pi := by
  let M := max 1 (max |freq| (max (2 / (∫ r, planarResolventMode r ^ 2)) (2 / Real.pi)))
  have hm : M ≤ (guard freq : ℝ) := by
    have hh := Nat.le_ceil M
    simp only [guard, Nat.cast_add, Nat.cast_one]
    linarith
  have h1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hf : |freq| ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have ha : 2 / (∫ r, planarResolventMode r ^ 2) ≤ M :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hp : 2 / Real.pi ≤ M :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  exact ⟨h1.trans hm, hf.trans hm,
    (div_le_iff₀ planarResolventMode_square_integral_positive).mp (ha.trans hm),
    (div_le_iff₀ Real.pi_pos).mp (hp.trans hm)⟩

theorem precision_bounds (rho P : ℕ) :
    (guard (GaussianFrequency.frequency rho) : ℝ) * ((precision rho P : ℝ) + 1)⁻¹ ≤ 1 ∧
      (factorBound (guard (GaussianFrequency.frequency rho)) : ℝ) *
        ((precision rho P : ℝ) + 1)⁻¹ ≤ ((P : ℝ) + 1)⁻¹ := by
  let C := (guard (GaussianFrequency.frequency rho) : ℝ)
  let K := (factorBound (guard (GaussianFrequency.frequency rho)) : ℝ)
  let S := (P : ℝ) + 1
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hS : 1 ≤ S := by
    dsimp [S]
    linarith [show (0 : ℝ) ≤ P from Nat.cast_nonneg _]
  have hN : (precision rho P : ℝ) = (C + K) * S := by
    simp only [precision, Nat.cast_mul, Nat.cast_add, Nat.cast_one, C, K, S]
  have hn : (0 : ℝ) < precision rho P + 1 := by positivity
  have hCa : C ≤ (precision rho P : ℝ) + 1 := by
    rw [hN]
    nlinarith [mul_nonneg hK (show 0 ≤ S by linarith)]
  have hKa : K * S ≤ (precision rho P : ℝ) + 1 := by
    rw [hN]
    nlinarith [mul_nonneg hC (show 0 ≤ S by linarith)]
  constructor
  · change C * ((precision rho P : ℝ) + 1)⁻¹ ≤ 1
    rw [← div_eq_mul_inv]
    exact (div_le_one hn).mpr hCa
  · change K * ((precision rho P : ℝ) + 1)⁻¹ ≤ S⁻¹
    rw [← div_eq_mul_inv, ← one_div]
    exact (div_le_div_iff₀ hn (by linarith : 0 < S)).mpr (by simpa using hKa)

theorem approximation_error (rho P : ℕ) :
    |(approximate rho P : ℝ) - coefficient (GaussianFrequency.frequency rho)| ≤
      ((P : ℝ) + 1)⁻¹ := by
  let N := precision rho P
  have hc := guard_bounds (GaussianFrequency.frequency rho)
  have hπ := PiProgram.error (8 * (N + 1)) (by omega)
  have hπ' : |(PiProgram.approximate (8 * (N + 1)) : ℝ) - Real.pi| ≤ ((N : ℝ) + 1)⁻¹ := by
    convert hπ using 1
    push_cast
    field_simp
  have h := coulomb_normalization_error hc.1 planarResolventMode_square_integral_positive
    Real.pi_pos hc.2.2.1 hc.2.2.2 hc.2.1 (by positivity) (precision_bounds rho P).1
    (NormalizationSchedule.approximation_error N) hπ' (GaussianFrequency.approximation_error rho N)
  have he : (factorBound (guard (GaussianFrequency.frequency rho)) : ℝ) =
      (guard (GaussianFrequency.frequency rho) : ℝ) ^ 3 +
        3 * (guard (GaussianFrequency.frequency rho) : ℝ) ^ 5 := by
    simp only [factorBound, Nat.cast_add, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  rw [← he] at h
  have h' : |(approximate rho P : ℝ) - coefficient (GaussianFrequency.frequency rho)| ≤
      (factorBound (guard (GaussianFrequency.frequency rho)) : ℝ) * ((N : ℝ) + 1)⁻¹ := by
    simpa only [approximate, coefficient, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, N] using h
  exact h'.trans (precision_bounds rho P).2

noncomputable opaque precisionProgram (rho : ℕ) : Procedure unaryCode unaryCode (precision rho) := by
  let c := Procedure.constant unaryCode unaryCode
    (guard (GaussianFrequency.frequency rho) + factorBound (guard (GaussianFrequency.frequency rho)))
  exact (ResolventSchedule.mulProgram.comp (c.pair Procedure.unarySuccessor)).congrFun (by intro P; rfl)

noncomputable opaque piCountProgram (rho : ℕ) : Procedure unaryCode unaryCode
    (fun P => 8 * (precision rho P + 1)) :=
  (ResolventSchedule.mulProgram.comp ((Procedure.constant unaryCode unaryCode 8).pair
    (Procedure.unarySuccessor.comp (precisionProgram rho)))).congrFun (by intro P; rfl)

noncomputable opaque program (rho : ℕ) : Procedure unaryCode ratCode (approximate rho) := by
  let n := precisionProgram rho
  let f := (GaussianFrequency.program rho).comp n
  let a := NormalizationSchedule.program.comp n
  let p := PiProgram.program.comp (piCountProgram rho)
  let a2 := Procedure.ratMul.comp (a.pair a)
  exact (Procedure.ratDiv.comp (f.pair (Procedure.ratMul.comp (a2.pair p)))).congrFun
    (by intro P; simp only [approximate, pow_two]; rfl)

noncomputable def certificate (rho : ℕ) :
    Turing.TM2ComputableInPolyTime unaryCode ratCode (approximate rho) := (program rho).toTM2

end ContinuumCoulomb.CoulombNormalization

end

end OAI
