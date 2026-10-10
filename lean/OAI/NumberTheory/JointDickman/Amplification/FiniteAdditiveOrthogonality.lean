import OAI.NumberTheory.JointDickman.Amplification.AdditivePhaseBridge
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! # Finite additive orthogonality for the arithmetic kernel -/

namespace JointDickman
open Finset MeasureTheory
open scoped ComplexConjugate

theorem additivePhase_conj (t : ℝ) : conj (additivePhase t) = additivePhase (-t) := by
  unfold additivePhase
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
  ring

theorem integral_additivePhase_int (k : ℤ) :
    (∫ θ in (0 : ℝ)..1, additivePhase ((k : ℝ)*θ)) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk,additivePhase]
  · have hc : (k : ℂ)*(2*(Real.pi : ℂ)*Complex.I) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast hk)
        (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
    have he : (fun θ : ℝ => additivePhase ((k : ℝ)*θ)) =
        (fun θ : ℝ => Complex.exp ((k : ℂ)*(2*(Real.pi : ℂ)*Complex.I)*θ)) := by
      funext θ
      unfold additivePhase
      congr 1
      push_cast
      ring
    rw [he,integral_exp_mul_complex hc]
    simp [hk,Complex.exp_int_mul_two_pi_mul_I]

noncomputable def finiteAdditiveSum (s : Finset ℕ) (c : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ s, c n*additivePhase ((n : ℝ)*θ)

theorem finiteAdditiveSum_continuous (s : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (finiteAdditiveSum s c) := by
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul (continuous_additivePhase.comp (continuous_const.mul continuous_id))

theorem integral_additive_pair (n m : ℕ) (c d : ℂ) :
    (∫ θ in (0 : ℝ)..1,
      (c*additivePhase ((n : ℝ)*θ))*conj (d*additivePhase ((m : ℝ)*θ))) =
      if n = m then c*conj d else 0 := by
  have he : (fun θ : ℝ => (c*additivePhase ((n : ℝ)*θ))*
      conj (d*additivePhase ((m : ℝ)*θ))) =
      (fun θ : ℝ => (c*conj d)*additivePhase (((n : ℤ)-m : ℤ)*θ)) := by
    funext θ
    rw [map_mul,additivePhase_conj]
    have hp : additivePhase (((n : ℤ)-m : ℤ)*θ) =
        additivePhase ((n : ℝ)*θ)*additivePhase (-((m : ℝ)*θ)) := by
      rw [← additivePhase_add]
      congr 1
      push_cast
      ring
    rw [hp]
    ring
  rw [he,intervalIntegral.integral_const_mul,integral_additivePhase_int]
  by_cases h : n = m
  · simp [h]
  · have h' : (n : ℤ)-(m : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    simp [h,h']

/-- The exact finite Parseval pairing; different supports are allowed. -/
theorem finiteAdditiveSum_pair_integral (s t : Finset ℕ) (c d : ℕ → ℂ) :
    (∫ θ in (0 : ℝ)..1, finiteAdditiveSum s c θ*conj (finiteAdditiveSum t d θ)) =
      ∑ n ∈ s, ∑ m ∈ t, if n = m then c n*conj (d m) else 0 := by
  have hcont (n m : ℕ) : Continuous (fun θ : ℝ =>
      (c n*additivePhase ((n : ℝ)*θ))*conj (d m*additivePhase ((m : ℝ)*θ))) :=
    (continuous_const.mul (continuous_additivePhase.comp (continuous_const.mul continuous_id))).mul
      (continuous_star.comp (continuous_const.mul
        (continuous_additivePhase.comp (continuous_const.mul continuous_id))))
  have hint (n m : ℕ) := (hcont n m).intervalIntegrable (μ := volume) 0 1
  simp only [finiteAdditiveSum,map_sum,mul_sum,sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [sum_comm]
    apply sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_finsetSum]
    · apply sum_congr rfl
      intro m hm
      exact integral_additive_pair m n (c m) (d n)
    · intro m _
      exact hint m n
  · intro n _
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro m _
    exact hcont m n

/-- Parseval for the finite trigonometric polynomials used in each box. -/
theorem finiteAdditiveSum_parseval (s : Finset ℕ) (c : ℕ → ℂ) :
    (∫ θ in (0 : ℝ)..1, ‖finiteAdditiveSum s c θ‖^2) = ∑ n ∈ s, ‖c n‖^2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he : (fun θ : ℝ => ((‖finiteAdditiveSum s c θ‖^2 : ℝ) : ℂ)) =
      (fun θ : ℝ => finiteAdditiveSum s c θ*conj (finiteAdditiveSum s c θ)) := by
    funext θ
    simp only [Complex.ofReal_pow,Complex.mul_conj']
  rw [he,finiteAdditiveSum_pair_integral]
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro n hn
  rw [sum_eq_single n]
  · simp [Complex.mul_conj']
  · intro m _ hmn
    simp [Ne.symm hmn]
  · exact fun h => (h hn).elim

end JointDickman

end OAI
