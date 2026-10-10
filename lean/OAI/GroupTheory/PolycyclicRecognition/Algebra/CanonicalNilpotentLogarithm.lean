import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteExponentialLogarithm

namespace OAI

/-! # A truncation-independent logarithm for unipotent elements -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A]

def nilpotentLog (a : A) : A :=
  finiteNilpotentLog (nilpotencyClass a + 1) a

theorem nilpotentLog_eq_of_pow (a : A) (ha : IsNilpotent a) (n : ℕ)
    (hn : a ^ (n + 1) = 0) : nilpotentLog a = finiteNilpotentLog (n + 1) a := by
  have hk : a ^ (nilpotencyClass a + 1) = 0 := by
    rw [pow_succ, pow_nilpotencyClass ha, zero_mul]
  let F := nilpotentPowerSeriesEval a (nilpotencyClass a) hk
  have hF : F PowerSeries.X ^ (n + 1) = 0 := by
    rw [nilpotentPowerSeriesEval_X]
    exact hn
  have h := rationalPowerSeriesHom_eq_aeval_trunc F hF (PowerSeries.log ℚ)
  rw [nilpotentPowerSeriesEval_X] at h
  exact h

theorem nilpotentLog_nilpotent (a : A) (ha : IsNilpotent a) :
    IsNilpotent (nilpotentLog a) := by
  have hk : a ^ (nilpotencyClass a + 1) = 0 := by
    rw [pow_succ, pow_nilpotencyClass ha, zero_mul]
  exact ⟨_, finiteNilpotentLog_pow a (nilpotencyClass a) hk⟩

theorem exp_nilpotentLog (a : A) (ha : IsNilpotent a) :
    IsNilpotent.exp (nilpotentLog a) = 1 + a := by
  apply exp_finiteNilpotentLog
  rw [pow_succ, pow_nilpotencyClass ha, zero_mul]

theorem nilpotentLog_exp (a : A) (ha : IsNilpotent a) :
    nilpotentLog (IsNilpotent.exp a - 1) = a := by
  have hk : a ^ (nilpotencyClass a + 1) = 0 := by
    rw [pow_succ, pow_nilpotencyClass ha, zero_mul]
  have he : (IsNilpotent.exp a - 1) ^ (nilpotencyClass a + 1) = 0 := by
    have h := nilpotentPowerSeriesEval_nilpotent a (nilpotencyClass a) hk
      (PowerSeries.exp ℚ - 1) (by simp)
    simpa only [map_sub, nilpotentPowerSeriesEval_exp, map_one] using h
  rw [nilpotentLog_eq_of_pow _ (IsNilpotent.isNilpotent_exp_sub_one ha) _ he]
  exact finiteNilpotentLog_exp a (nilpotencyClass a) hk

theorem nilpotentLog_map {B : Type*} [Ring B] [Algebra ℚ B]
    (f : A →+* B) (a : A) (ha : IsNilpotent a) :
    nilpotentLog (f a) = f (nilpotentLog a) := by
  have hk : a ^ (nilpotencyClass a + 1) = 0 := by
    rw [pow_succ, pow_nilpotencyClass ha, zero_mul]
  have hf : (f a) ^ (nilpotencyClass a + 1) = 0 := by rw [← map_pow, hk, map_zero]
  let F := f.comp (nilpotentPowerSeriesEval a (nilpotencyClass a) hk)
  have hF : F PowerSeries.X ^ (nilpotencyClass a + 1) = 0 := by
    change f (nilpotentPowerSeriesEval a (nilpotencyClass a) hk PowerSeries.X) ^ _ = 0
    rwa [nilpotentPowerSeriesEval_X]
  have h := rationalPowerSeriesHom_eq_aeval_trunc F hF (PowerSeries.log ℚ)
  have hx : F PowerSeries.X = f a := by
    simp only [F, RingHom.comp_apply, nilpotentPowerSeriesEval_X]
  rw [hx] at h
  change f (nilpotentLog a) = finiteNilpotentLog (nilpotencyClass a + 1) (f a) at h
  rw [nilpotentLog_eq_of_pow _ ⟨_, hf⟩ _ hf]
  exact h.symm

end PolycyclicRecognition

end

end OAI
