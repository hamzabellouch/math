import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- The integer remainder in the ceiling descent is exactly the canonical
representative of the negative residue, including remainder zero. -/
theorem least_remainder_eq_neg_cast_val {u A z : ℕ} [NeZero u]
    (hlo : A ≤ u * z) (hhi : u * z < A + u) :
    u * z - A = (-(A : ZMod u)).val := by
  have hr : u * z - A < u := by omega
  have hc : ((u * z - A : ℕ) : ZMod u) = -(A : ZMod u) := by
    rw [Nat.cast_sub hlo, Nat.cast_mul]
    simp
  have hv := congrArg ZMod.val hc
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hr] using hv

/-- Natural rational ceiling supplies the exact least-residue integer. -/
theorem ceiling_remainder_eq_neg_cast_val {u A : ℕ} [NeZero u] :
    u * ⌈(A : ℚ) / (u : ℚ)⌉₊ - A = (-(A : ZMod u)).val := by
  have hu : (0 : ℚ) < u := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne u)
  let z : ℕ := ⌈(A : ℚ) / (u : ℚ)⌉₊
  have hloQ : (A : ℚ) ≤ (u : ℚ) * z := by
    have h := (div_le_iff₀ hu).mp (Nat.le_ceil ((A : ℚ) / (u : ℚ)))
    simpa only [mul_comm] using h
  have hhiQ : (u : ℚ) * z < (A : ℚ) + u := by
    have h := mul_lt_mul_of_pos_right
      (Nat.ceil_lt_add_one (by positivity : (0 : ℚ) ≤ (A : ℚ) / (u : ℚ))) hu
    dsimp [z]
    rw [add_mul, div_mul_cancel₀ _ hu.ne', one_mul] at h
    simpa only [mul_comm] using h
  exact least_remainder_eq_neg_cast_val (by exact_mod_cast hloQ) (by exact_mod_cast hhiQ)

/-- Consequently the natural small-remainder condition is literally the
initial cyclic interval condition used in Fourier smoothing. -/
theorem ceiling_remainder_lt_iff {u A : ℕ} [NeZero u] (B : ℝ) :
    ((u * ⌈(A : ℚ) / (u : ℚ)⌉₊ - A : ℕ) : ℝ) < B ↔
      (((-(A : ZMod u)).val : ℕ) : ℝ) < B := by
  rw [ceiling_remainder_eq_neg_cast_val]

/-- Standard additive characters at natural residues are the usual
exponential phases without choosing a representative. -/
theorem stdAddChar_nat_phase {u : ℕ} [NeZero u] (A : ℕ) :
    ZMod.stdAddChar (A : ZMod u) =
      Complex.exp (2 * Real.pi * Complex.I * (A : ℂ) / (u : ℂ)) := by
  simpa only [Int.cast_natCast] using (ZMod.stdAddChar_coe (N := u) (A : ℤ))

/-- In particular, the positive Fourier coefficient for natural products is
exactly the exponential sum in the residue estimates. -/
theorem stdAddChar_nat_product_phase {u : ℕ} [NeZero u] (l A : ℕ) :
    ZMod.stdAddChar ((l : ZMod u) * (A : ZMod u)) =
      Complex.exp (2 * Real.pi * Complex.I * (l * A : ℕ) / (u : ℂ)) := by
  rw [← Nat.cast_mul, stdAddChar_nat_phase]

/-- Passing from positive exponential phases to the negative least-residue
phases preserves every Fourier coefficient norm. -/
theorem norm_neg_residue_fourier_eq {u : ℕ} [NeZero u]
    {I : Type*} [Fintype I] (A : I → ℕ) (l : ℕ) :
    ‖∑ t : I, ZMod.stdAddChar ((l : ZMod u) * (-(A t : ZMod u)))‖ =
      ‖∑ t : I, Complex.exp
        (2 * Real.pi * Complex.I * (l * A t : ℕ) / (u : ℂ))‖ := by
  simp_rw [mul_neg, AddChar.map_neg_eq_conj]
  rw [← map_sum (starRingEnd ℂ)
    (fun t : I => ZMod.stdAddChar ((l : ZMod u) * (A t : ZMod u))) Finset.univ]
  rw [Complex.norm_conj]
  simp_rw [stdAddChar_nat_product_phase]

/-- The normalized-average version used by the discrepancy estimate. -/
theorem norm_neg_residue_fourier_average_eq {u : ℕ} [NeZero u]
    {I : Type*} [Fintype I] (A : I → ℕ) (l : ℕ) :
    ‖(∑ t : I, ZMod.stdAddChar ((l : ZMod u) * (-(A t : ZMod u)))) /
        (Fintype.card I : ℂ)‖ =
      ‖(∑ t : I, Complex.exp
        (2 * Real.pi * Complex.I * (l * A t : ℕ) / (u : ℂ))) /
          (Fintype.card I : ℂ)‖ := by
  rw [norm_div, norm_div, norm_neg_residue_fourier_eq]

end Problem337

end

end OAI
