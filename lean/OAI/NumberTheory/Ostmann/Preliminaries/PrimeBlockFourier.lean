import OAI.NumberTheory.Ostmann.Preliminaries.ProjectedMass
import OAI.NumberTheory.Ostmann.SharpSieve
import OAI.NumberTheory.Ostmann.Supply.FiniteParseval

namespace OAI

namespace Ostmann.Preliminaries
open scoped BigOperators

noncomputable def uniformResidueMass (U : Finset ℕ) (p : ℕ) [NeZero p] : ZMod p → ℝ :=
  projectedMass (fun a : U => (a.val : ZMod p)) (fun _ => (U.card : ℝ)⁻¹)

theorem uniformResidueMass_sum (U : Finset ℕ) (hU : U.Nonempty)
    (p : ℕ) [NeZero p] : ∑ r, uniformResidueMass U p r = 1 := by
  rw [uniformResidueMass, projectedMass_sum]
  have hc : (U.card : ℝ) ≠ 0 := by exact_mod_cast hU.card_ne_zero
  simp [hc]

theorem stdAddChar_nat_mul (p n : ℕ) [NeZero p] (a : ZMod p) :
    ZMod.stdAddChar ((n : ZMod p) * a) =
      Complex.exp (2 * Real.pi * Complex.I * n * ((a.val : ℝ) / p)) := by
  calc
    ZMod.stdAddChar ((n : ZMod p) * a) =
        ZMod.stdAddChar ((((n * a.val : ℕ) : ℤ)) : ZMod p) := by
      congr 1
      simp
    _ = _ := by
      rw [ZMod.stdAddChar_coe]
      push_cast
      congr 1
      ring

theorem dft_uniformResidueMass (U : Finset ℕ) (p : ℕ) [NeZero p] (a : ZMod p) :
    ZMod.dft (fun r => (uniformResidueMass U p r : ℂ)) (-a) =
      Ostmann.normalizedExpSum U ((a.val : ℝ) / p) := by
  simp only [ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg]
  simp_rw [mul_comm (ZMod.stdAddChar _) _]
  rw [uniformResidueMass, projectedMass_complex_test]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast, ← Finset.mul_sum]
  simp_rw [stdAddChar_nat_mul]
  rw [Finset.sum_coe_sort U (fun n : ℕ =>
    Complex.exp (2 * Real.pi * Complex.I * n * ((a.val : ℝ) / p)))]
  simp only [Ostmann.normalizedExpSum, div_eq_mul_inv]
  push_cast
  ring

theorem dft_real_positive_parseval (p : ℕ) [NeZero p] (μ : ZMod p → ℝ) :
    ∑ a, ‖ZMod.dft (fun r => (μ r : ℂ)) (-a)‖ ^ 2 =
      (p : ℝ) * massEnergy μ := by
  have hneg := Equiv.sum_comp (Equiv.neg (ZMod p))
    (fun a => ‖ZMod.dft (fun r => (μ r : ℂ)) a‖ ^ 2)
  simp only [Equiv.neg_apply] at hneg
  rw [hneg]
  rw [Ostmann.Supply.dft_parseval]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, massEnergy]

theorem dft_nonzero_energy_eq (p : ℕ) [NeZero p] (μ : ZMod p → ℝ)
    (hmass : ∑ r, μ r = 1) :
    (∑ a ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      ‖ZMod.dft (fun r => (μ r : ℂ)) (-a)‖ ^ 2) =
      (p : ℝ) * massEnergy μ - 1 := by
  have hzero : ZMod.dft (fun r => (μ r : ℂ)) (0 : ZMod p) = 1 := by
    simp [ZMod.dft_apply, ← Complex.ofReal_sum, hmass]
  have h := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
    (fun a => ‖ZMod.dft (fun r => (μ r : ℂ)) (-a)‖ ^ 2) (by simp : (0 : ZMod p) ∈ Finset.univ)
  rw [dft_real_positive_parseval] at h
  simp only [neg_zero, hzero, norm_one, one_pow] at h
  linarith

theorem nonzero_energy_ge_forbidden (p : ℕ) [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (μ : ZMod p → ℝ)
    (hmass : ∑ r, μ r = 1) (hsupp : ∀ r ∉ S, μ r = 0) :
    ((p : ℝ) - S.card) / p ≤
      ∑ a ∈ (Finset.univ : Finset (ZMod p)).erase 0,
        ‖ZMod.dft (fun r => (μ r : ℂ)) (-a)‖ ^ 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hs : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hsp : (S.card : ℝ) ≤ p := by exact_mod_cast (Finset.card_le_univ S |>.trans_eq (ZMod.card p))
  have he := uniformDefect_nonneg S μ
  rw [uniformDefect_eq_energy_sub S hS μ hmass hsupp] at he
  have hrecip : (S.card : ℝ)⁻¹ ≤ massEnergy μ := by linarith
  have hone : 1 ≤ (S.card : ℝ) * massEnergy μ := by
    have h := mul_le_mul_of_nonneg_left hrecip hs.le
    simpa [hs.ne'] using h
  rw [dft_nonzero_energy_eq p μ hmass]
  apply (div_le_iff₀ hp).mpr
  have he0 := massEnergy_nonneg μ
  have hmul := mul_nonneg (sub_nonneg.mpr hsp) he0
  nlinarith

end Ostmann.Preliminaries

end OAI
