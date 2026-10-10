import OAI.GroupTheory.PolycyclicRecognition.Algebra.CanonicalNilpotentLogarithm
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! # Exponential products with a common nilpotent scalar -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem nilpotent_exp_sub_one_factor (a : A) (ha : IsNilpotent a) :
    ∃ b : A, IsNilpotent.exp a - 1 = a * b := by
  have hn : a ^ (nilpotencyClass a + 1) = 0 := by
    rw [pow_succ, pow_nilpotencyClass ha, zero_mul]
  let F := nilpotentPowerSeriesEval a (nilpotencyClass a) hn
  have hc : (PowerSeries.exp ℚ - 1).constantCoeff = 0 := by simp
  obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr hc
  refine ⟨F q, ?_⟩
  calc
    IsNilpotent.exp a - 1 = F (PowerSeries.exp ℚ - 1) := by
      rw [map_sub, nilpotentPowerSeriesEval_exp, map_one]
    _ = a * F q := by rw [hq, map_mul, nilpotentPowerSeriesEval_X]

variable {R : Type*} [CommRing R] [Algebra R A]

theorem scalar_nilpotent_exp_product_factor (t : R) (ht : IsNilpotent t) (L : List A) :
    ∃ b : A, (L.map (fun a => IsNilpotent.exp (t • a))).prod - 1 = t • b := by
  have hn (a : A) : IsNilpotent (t • a) := by
    obtain ⟨k, hk⟩ := ht
    exact ⟨k, by rw [smul_pow, hk, zero_smul]⟩
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons a L ih =>
    obtain ⟨b, hb⟩ := nilpotent_exp_sub_one_factor (t • a) (hn a)
    obtain ⟨c, hc⟩ := ih
    refine ⟨(a * b) * (L.map (fun a => IsNilpotent.exp (t • a))).prod + c, ?_⟩
    rw [List.map_cons, List.prod_cons, smul_add, ← smul_mul_assoc,
      ← smul_mul_assoc, ← hb, ← hc]
    noncomm_ring

theorem scalar_nilpotent_exp_product_pow (t : R) (N : ℕ) (ht : t ^ N = 0) (L : List A) :
    ((L.map (fun a => IsNilpotent.exp (t • a))).prod - 1) ^ N = 0 := by
  obtain ⟨b, hb⟩ := scalar_nilpotent_exp_product_factor t ⟨N, ht⟩ L
  rw [hb, smul_pow, ht, zero_smul]

end PolycyclicRecognition

end

end OAI
