import OAI.NumberTheory.Ostmann.QuadraticCenter.UniformPhaseGrid
import OAI.NumberTheory.Ostmann.Characters.AdditiveFourier
import OAI.NumberTheory.Ostmann.Characters.WeightedPhaseExtraction

namespace OAI

/-! # Uniform linear-phase sums of a periodic function from Fourier coefficient bounds -/

namespace Ostmann

open scoped BigOperators

theorem stdAddChar_eq_realPhase {q : ℕ} [NeZero q] (u : ZMod q) :
    ZMod.stdAddChar u = realAdditivePhase ((u.val : ℝ) / q) := by
  calc
    _ = ZMod.stdAddChar ((u.val : ℕ) : ZMod q) := by rw [ZMod.natCast_zmod_val]
    _ = Complex.exp (2 * Real.pi * Complex.I * (u.val : ℂ) / q) := by
      rw [← Int.cast_natCast, ZMod.stdAddChar_coe]
      push_cast
      rfl
    _ = _ := by
      unfold realAdditivePhase
      congr 1
      push_cast
      ring

theorem stdAddChar_mul_natCast {q : ℕ} [NeZero q] (u : ZMod q) (n : ℕ) :
    ZMod.stdAddChar (u * (n : ZMod q)) = ZMod.stdAddChar u ^ n := by
  induction n with
  | zero => simp [AddChar.map_zero_eq_one]
  | succ n ih => simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one,
      AddChar.map_add_eq_mul, ih, pow_succ]

theorem periodic_linear_phase_expansion (q : ℕ) [NeZero q]
    (f : ZMod q → ℂ) (α : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, f (n : ZMod q) * realAdditivePhase α ^ n) =
      ∑ u : ZMod q, additiveFourier f u *
        ∑ n ∈ Finset.range N, realAdditivePhase (α + (u.val : ℝ) / q) ^ n := by
  simp_rw [additiveFourier_inversion f, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [stdAddChar_mul_natCast, stdAddChar_eq_realPhase, realAdditivePhase_add, mul_pow]
  ring

theorem periodic_linear_phase_sum_bound (q : ℕ) [NeZero q]
    (f : ZMod q → ℂ) (A α : ℝ) (hA : 0 ≤ A)
    (hf : ∀ u, ‖additiveFourier f u‖ ≤ A) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, f (n : ZMod q) * realAdditivePhase α ^ n‖ ≤
      2 * A * ((N : ℝ) + q * (1 + Real.log q)) := by
  rw [periodic_linear_phase_expansion]
  have hgrid : (∑ u : ZMod q, ‖∑ n ∈ Finset.range N,
      realAdditivePhase (α + (u.val : ℝ) / q) ^ n‖) ≤
        2 * ((N : ℝ) + q * (1 + Real.log q)) := by
    have he := (ZMod.finEquiv q).toEquiv.sum_comp (fun u =>
      ‖∑ n ∈ Finset.range N, realAdditivePhase (α + (u.val : ℝ) / q) ^ n‖)
    have heq (i : Fin q) : ((ZMod.finEquiv q).toEquiv i).val = i.val := by
      cases q with
      | zero => exact Fin.elim0 i
      | succ q => rfl
    simp_rw [heq] at he
    exact he.symm.trans_le (uniform_phase_grid_bound q α N)
  calc
    _ ≤ ∑ u : ZMod q, ‖additiveFourier f u *
        ∑ n ∈ Finset.range N, realAdditivePhase (α + (u.val : ℝ) / q) ^ n‖ := norm_sum_le _ _
    _ ≤ ∑ u : ZMod q, A * ‖∑ n ∈ Finset.range N,
        realAdditivePhase (α + (u.val : ℝ) / q) ^ n‖ := by
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hf u) (norm_nonneg _)
    _ = A * (∑ u : ZMod q, ‖∑ n ∈ Finset.range N,
        realAdditivePhase (α + (u.val : ℝ) / q) ^ n‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ A * (2 * ((N : ℝ) + q * (1 + Real.log q))) :=
      mul_le_mul_of_nonneg_left hgrid hA
    _ = _ := by ring

theorem weighted_periodic_linear_phase_bound (q : ℕ) [NeZero q]
    (f : ZMod q → ℂ) (A α : ℝ) (hA : 0 ≤ A)
    (hf : ∀ u, ‖additiveFourier f u‖ ≤ A) (w : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w n * (f (n : ZMod q) * realAdditivePhase α ^ n)‖ ≤
      discreteVariation w N * (2 * A * ((N : ℝ) + q * (1 + Real.log q))) := by
  apply weighted_sum_le_variation
  intro n hn
  apply (periodic_linear_phase_sum_bound q f A α hA hf n).trans
  have hnn : (n : ℝ) ≤ N := by exact_mod_cast hn
  exact mul_le_mul_of_nonneg_left (add_le_add_left hnn _) (by positivity)

end Ostmann

end OAI
