import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import OAI.NumberTheory.SiegelZeros.EntireFunctions.ZeroContribution

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W51

variable {q : ℕ} [NeZero q]

noncomputable def normalizedCompletion (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s / 2) * DirichletCharacter.completedLFunction χ s

theorem conductorFactor_ne_zero (s : ℂ) : (q : ℂ) ^ (s / 2) ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))

theorem differentiable_conductorFactor :
    Differentiable ℂ (fun s : ℂ => (q : ℂ) ^ (s / 2)) :=
  (differentiable_id.div_const 2).const_cpow
    (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))

theorem differentiable_normalizedCompletion (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Differentiable ℂ (normalizedCompletion χ) :=
  differentiable_conductorFactor.mul (DirichletCharacter.differentiable_completedLFunction hχ)

theorem normalizedCompletion_zero_iff (χ : DirichletCharacter ℂ q) (s : ℂ) :
    normalizedCompletion χ s = 0 ↔ DirichletCharacter.completedLFunction χ s = 0 := by
  simp only [normalizedCompletion, mul_eq_zero, conductorFactor_ne_zero, false_or]

theorem LFunction_zero_iff_normalizedCompletion_zero (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = 0 ↔ normalizedCompletion χ s = 0 := by
  rw [normalizedCompletion_zero_iff]
  exact W03.LFunction_zero_iff_completed_zero χ hs

theorem normalizedCompletion_ne_zero_of_one_le_re (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) : normalizedCompletion χ s ≠ 0 := by
  intro hz
  have hs0 : 0 < s.re := lt_of_lt_of_le zero_lt_one hs
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs
    ((LFunction_zero_iff_normalizedCompletion_zero χ hs0).mpr hz)

theorem normalizedCompletion_one_sub (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (s : ℂ) :
    normalizedCompletion χ (1 - s) =
      DirichletCharacter.rootNumber χ * normalizedCompletion χ⁻¹ s := by
  unfold normalizedCompletion
  rw [hχ.completedLFunction_one_sub]
  have hp : (q : ℂ) ^ ((1 - s) / 2) * (q : ℂ) ^ (s - 1 / 2) =
      (q : ℂ) ^ (s / 2) := by
    rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr (NeZero.ne q))]
    congr 1
    ring
  calc
    (q : ℂ) ^ ((1 - s) / 2) *
        ((q : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ *
          DirichletCharacter.completedLFunction χ⁻¹ s) =
        ((q : ℂ) ^ ((1 - s) / 2) * (q : ℂ) ^ (s - 1 / 2)) *
          (DirichletCharacter.rootNumber χ * DirichletCharacter.completedLFunction χ⁻¹ s) := by
            ring
    _ = _ := by rw [hp]; ring

theorem logDeriv_conductorFactor (s : ℂ) :
    logDeriv (fun z : ℂ => (q : ℂ) ^ (z / 2)) s = Complex.log (q : ℂ) / 2 := by
  have hd := ((hasDerivAt_id s).div_const (2 : ℂ)).const_cpow
    (Or.inl (show (q : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne q)))
  simp only [id_eq] at hd
  rw [logDeriv_apply, hd.deriv]
  field_simp [conductorFactor_ne_zero (q := q) s]

theorem logDeriv_normalizedCompletion (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : DirichletCharacter.completedLFunction χ s ≠ 0) :
    logDeriv (normalizedCompletion χ) s = Complex.log (q : ℂ) / 2 +
      logDeriv (DirichletCharacter.completedLFunction χ) s := by
  unfold normalizedCompletion
  rw [logDeriv_fun_mul s (conductorFactor_ne_zero (q := q) s) hs
    (differentiable_conductorFactor s)
    (DirichletCharacter.differentiable_completedLFunction hχ s), logDeriv_conductorFactor]

end SiegelZerosAwei.W51

end

end SiegelZeros

end OAI
