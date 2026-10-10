import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarCalibration
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Uniform polynomial amplification of the actual hopping brackets. A fixed
large power of the input-size parameter suffices; the well constants and
contact tolerance remain fixed. -/

noncomputable section
open Filter
open scoped Topology
namespace ContinuumCoulomb

theorem planar_polynomial_brackets {A k : ℕ} {ε N : ℝ}
    (hε : 0 ≤ ε) (_hε₁ : ε ≤ 1) (hN : 2 ≤ N)
    (hd : 2 ≤ (1 - ε) * ((k : ℝ) * Real.log N))
    (hγ : 0 ≤ (k : ℝ) * ε - ((A : ℝ) + 1))
    (hlo : (k : ℝ) + 3 ≤ planarHoppingLowerConstant *
      (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1)))
    (hhi : planarHoppingUpperConstant * (2 * (k : ℝ) + 1) ≤
      (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1))) :
    N ^ A ≤ Real.exp ((k : ℝ) * Real.log N) *
      planarHopping ((1 - ε) * ((k : ℝ) * Real.log N)) ∧
    Real.exp ((k : ℝ) * Real.log N) *
      planarHopping ((1 + ε) * ((k : ℝ) * Real.log N)) ≤ (N ^ A)⁻¹ := by
  have hNpos : 0 < N := by linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlogN : Real.log N ≤ N := (Real.log_le_sub_one_of_pos hNpos).trans (by linarith)
  let γ : ℝ := (k : ℝ) * ε - ((A : ℝ) + 1)
  have hp : (2 : ℝ) ^ γ ≤ N ^ γ := Real.rpow_le_rpow (by norm_num) hN hγ
  have hloN : (k : ℝ) + 3 ≤ planarHoppingLowerConstant * N ^ γ :=
    hlo.trans (mul_le_mul_of_nonneg_left hp planarHoppingLowerConstant_positive.le)
  have hhiN : planarHoppingUpperConstant * (2 * (k : ℝ) + 1) ≤ N ^ γ := hhi.trans hp
  have hexp : Real.exp (ε * ((k : ℝ) * Real.log N)) = N ^ A * N * N ^ γ := by
    calc
      _ = N ^ ((A : ℝ) + 1 + γ) := by
        rw [Real.rpow_def_of_pos hNpos]
        congr 1
        dsimp [γ]
        ring
      _ = (N ^ (A : ℝ) * N ^ (1 : ℝ)) * N ^ γ := by
        rw [Real.rpow_add hNpos, Real.rpow_add hNpos]
      _ = _ := by rw [Real.rpow_natCast, Real.rpow_one]
  have hshort : (1 - ε) * ((k : ℝ) * Real.log N) + 3 ≤ ((k : ℝ) + 3) * N := by
    have hD : (1 - ε) * ((k : ℝ) * Real.log N) ≤ (k : ℝ) * Real.log N := by
      nlinarith [mul_nonneg hk hlog]
    have hkn := mul_le_mul_of_nonneg_left hlogN hk
    nlinarith
  have hlong : (1 + ε) * ((k : ℝ) * Real.log N) + 1 ≤ (2 * (k : ℝ) + 1) * N := by
    have hD : (1 + ε) * ((k : ℝ) * Real.log N) ≤ 2 * ((k : ℝ) * Real.log N) := by
      nlinarith [mul_nonneg hk hlog]
    have hkn := mul_le_mul_of_nonneg_left hlogN hk
    nlinarith
  have hD : 0 ≤ (k : ℝ) * Real.log N := mul_nonneg hk hlog
  have horder : (1 - ε) * ((k : ℝ) * Real.log N) ≤
      (1 + ε) * ((k : ℝ) * Real.log N) := by nlinarith
  constructor
  · apply le_trans _ (planarHopping_short_scaled hd)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    calc
      _ ≤ N ^ A * (((k : ℝ) + 3) * N) :=
        mul_le_mul_of_nonneg_left hshort (pow_nonneg hNpos.le _)
      _ ≤ N ^ A * ((planarHoppingLowerConstant * N ^ γ) * N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hloN hNpos.le)
          (pow_nonneg hNpos.le _)
      _ = _ := by rw [hexp]; ring
  · apply le_trans (planarHopping_long_scaled (hd.trans horder))
    rw [show -ε * ((k : ℝ) * Real.log N) = -(ε * ((k : ℝ) * Real.log N)) by ring,
      Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), hexp]
    have hpA : N ^ A ≠ 0 := pow_ne_zero _ hNpos.ne'
    calc
      _ ≤ planarHoppingUpperConstant * ((2 * (k : ℝ) + 1) * N) :=
        mul_le_mul_of_nonneg_left hlong planarHoppingUpperConstant_positive.le
      _ ≤ N ^ γ * N := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hhiN hNpos.le
      _ = _ := by field_simp

end ContinuumCoulomb

end

end OAI
