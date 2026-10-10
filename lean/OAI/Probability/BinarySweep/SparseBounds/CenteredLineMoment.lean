import Mathlib
import OAI.Probability.BinarySweep.Trajectories.FallingMoment

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
open Polynomial

lemma lineMoment_stein (m h : ℕ) (P : ℝ[X]) (hp : h+P.natDegree < m) :
    lineMoment m h (stein m h P) = 0 := by
  let L := (lineMoment m h).comp (stein m h)
  change L P = 0
  conv_lhs => rw [← P.sum_monomial_eq]
  simp only [Polynomial.sum_def,map_sum]
  apply Finset.sum_eq_zero
  intro n hn
  exact lineMoment_stein_monomial (show h+n < m from lt_of_le_of_lt
    (Nat.add_le_add_left (le_natDegree_of_ne_zero (mem_support_iff.mp hn)) h) hp) _

lemma lineMoment_C_mul (m h : ℕ) (a : ℝ) (P : ℝ[X]) :
    lineMoment m h (C a * P) = a * lineMoment m h P := by
  rw [← smul_eq_C_mul,map_smul,smul_eq_mul]

def centeredLineMoment (m h u v : ℕ) : ℝ :=
  lineMoment m h (X^v*(X-1)^u)

@[simp] lemma centeredLineMoment_zero (m h v : ℕ) :
    centeredLineMoment m h 0 v = fallingMoment m h v := by
  simp only [centeredLineMoment,pow_zero,mul_one,lineMoment_X_pow]

lemma X_derivative_X_pow (v : ℕ) :
    (X:ℝ[X]) * derivative (X^v) = C (v:ℝ) * X^v := by
  cases v with
  | zero => simp
  | succ v => simp only [derivative_X_pow, Nat.add_sub_cancel]; ring

lemma stein_centered (m h u v : ℕ) :
    stein m h (X^v*(X-1)^(u+1)) =
      C ((m:ℝ)-h-v-u-1) * (X^v*(X-1)^(u+2)) -
      C ((h:ℝ)+v+2*u+2) * (X^v*(X-1)^(u+1)) -
      C ((u:ℝ)+1) * (X^v*(X-1)^u) := by
  rw [stein_apply,derivative_mul]
  have hv := X_derivative_X_pow v
  have hd : derivative ((X-1)^(u+1) : ℝ[X]) = C ((u:ℝ)+1)*(X-1)^u := by
    simp [derivative_pow,derivative_sub,Nat.cast_add]
  rw [hd]
  have he : (X:ℝ[X])^2 * (derivative (X^v)*(X-1)^(u+1)) =
      C (v:ℝ)*X^(v+1)*(X-1)^(u+1) := by
    rw [show (X:ℝ[X])^2 * (derivative (X^v)*(X-1)^(u+1)) =
      X * (X*derivative (X^v))*(X-1)^(u+1) from by ring,hv,pow_succ]
    ring
  rw [mul_add,he]
  simp only [map_sub,map_add,map_mul,map_one,C_ofNat,pow_succ]
  ring

lemma centeredLineMoment_recurrence {m h u v : ℕ} (hu : h+v+u+1 < m) :
    ((m:ℝ)-h-v-u-1) * centeredLineMoment m h (u+2) v =
      ((h:ℝ)+v+2*u+2) * centeredLineMoment m h (u+1) v +
      ((u:ℝ)+1) * centeredLineMoment m h u v := by
  have hp : (X^v*(X-1)^(u+1) : ℝ[X]).natDegree ≤ v+(u+1) := by
    apply natDegree_mul_le.trans
    simp only [natDegree_pow,natDegree_X,mul_one]
    exact Nat.add_le_add_left (by simpa using
      (Nat.mul_le_mul_left (u+1) (natDegree_X_sub_C_le (1:ℝ)))) v
  have hs := lineMoment_stein m h (X^v*(X-1)^(u+1)) (by omega)
  rw [stein_centered] at hs
  simp only [LinearMap.map_sub,lineMoment_C_mul] at hs
  change _ * centeredLineMoment m h (u+2) v -
    _ * centeredLineMoment m h (u+1) v - _ * centeredLineMoment m h u v = 0 at hs
  linarith

lemma centeredLineMoment_one {m h v : ℕ} (hv : h+v < m) :
    ((m:ℝ)-h-v) * centeredLineMoment m h 1 v =
      ((h:ℝ)+v) * fallingMoment m h v := by
  have he : centeredLineMoment m h 1 v =
      fallingMoment m h (v+1) - fallingMoment m h v := by
    rw [centeredLineMoment,pow_one,mul_sub,mul_one,← pow_succ,map_sub,
      lineMoment_X_pow,lineMoment_X_pow]
  rw [he]
  have hh := fallingMoment_succ hv
  linear_combination hh

end BinaryCoordinateSweeps.Sparse

end

end OAI
