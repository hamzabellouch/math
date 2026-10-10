import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalPowerSeriesHom
import Mathlib.RingTheory.PowerSeries.Substitution

namespace OAI

/-! # Substitution under finite power-series evaluation -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A] (a : A) (n : ℕ) (ha : a ^ (n + 1) = 0)

theorem nilpotentPowerSeriesEval_X :
    nilpotentPowerSeriesEval a n ha PowerSeries.X = a := by
  rw [← Polynomial.coe_X, nilpotentPowerSeriesEval_coe, Polynomial.aeval_X]

theorem nilpotentPowerSeriesEval_nilpotent (g : PowerSeries ℚ)
    (hg : g.constantCoeff = 0) :
    nilpotentPowerSeriesEval a n ha g ^ (n + 1) = 0 := by
  obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr hg
  rw [← map_pow, hq, mul_pow, map_mul, map_pow, nilpotentPowerSeriesEval_X, ha, zero_mul]

theorem nilpotentPowerSeriesEval_subst (f g : PowerSeries ℚ)
    (hg : g.constantCoeff = 0) :
    nilpotentPowerSeriesEval a n ha (PowerSeries.subst g f) =
      Polynomial.aeval (nilpotentPowerSeriesEval a n ha g) (PowerSeries.trunc (n + 1) f) := by
  let S : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ :=
    PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' hg)
  let F := (nilpotentPowerSeriesEval a n ha).comp S.toRingHom
  have hX : F PowerSeries.X = nilpotentPowerSeriesEval a n ha g := by
    change nilpotentPowerSeriesEval a n ha (S PowerSeries.X) = _
    congr 1
    exact PowerSeries.substAlgHom_X (R := ℚ) (PowerSeries.HasSubst.of_constantCoeff_zero' hg)
  have hnil : F PowerSeries.X ^ (n + 1) = 0 := by
    rw [hX]
    exact nilpotentPowerSeriesEval_nilpotent a n ha g hg
  have h := rationalPowerSeriesHom_eq_aeval_trunc F hnil f
  rw [hX] at h
  change nilpotentPowerSeriesEval a n ha (S f) = _ at h
  simpa only [S, PowerSeries.coe_substAlgHom] using h

end PolycyclicRecognition

end

end OAI
