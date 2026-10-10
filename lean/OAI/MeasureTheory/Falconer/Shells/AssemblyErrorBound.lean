import OAI.MeasureTheory.Falconer.Estimates.RestorationSeries

namespace OAI

/-! # Converting the original-pair deletion bound to its summable majorant -/

namespace Falconer
open scoped ENNReal

theorem dyadic_leaf_error (N : ℕ) :
    ((2:ℝ≥0∞)^(2*N))⁻¹ = ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ)) := by
  have hfin : ((2:ℝ≥0∞)^(2*N))⁻¹ ≠ ∞ := by simp
  rw [← ENNReal.ofReal_toReal hfin]
  congr 1
  simp only [ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  rw [Real.rpow_neg (by positivity),Real.rpow_two]
  congr 1
  rw [← pow_mul,Nat.mul_comm N 2]

theorem class_discard_numeric (N k : ℕ) (lam : ℝ) :
    ((2:ℝ≥0∞)^(2*N))⁻¹ + (N^k:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-lam)) ≤
      ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ) + ((N:ℝ)+1)^k*((2:ℝ)^N)^(-lam)) := by
  have hp : ((N^k:ℕ):ℝ≥0∞) ≤ ENNReal.ofReal (((N:ℝ)+1)^k) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Nat.cast_pow] using pow_le_pow_left₀ (Nat.cast_nonneg N)
      (show (N:ℝ) ≤ N+1 by linarith) k
  rw [dyadic_leaf_error]
  apply (add_le_add le_rfl (mul_le_mul' hp le_rfl)).trans_eq
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add (by positivity) (by positivity)]

theorem restoration_numeric_bound (N k₁ k₂ : ℕ) {Cw Ccap c lam σ : ℝ}
    (hw : 0 ≤ Cw) (hcap : 0 ≤ Ccap) {D X₁ X₂ V : ℝ≥0∞}
    (hD : D ≤ ENNReal.ofReal (Ccap*((2:ℝ)^N)^(-c)))
    (h₁ : X₁ ≤ ((2:ℝ≥0∞)^(2*N))⁻¹ + (N^k₁:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
    (h₂ : X₂ ≤ ((2:ℝ≥0∞)^(2*N))⁻¹ + (N^k₂:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
    (hV : V ≤ ENNReal.ofReal Cw * (D + (X₁ + X₂ +
      (4*(N+1)^2:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-σ))))) :
    V ≤ ENNReal.ofReal (restorationError Cw Ccap c lam σ k₁ k₂ N) := by
  apply hV.trans
  have ht : (4*(N+1)^2:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-σ)) =
      ENNReal.ofReal (4*((N:ℝ)+1)^2*((2:ℝ)^N)^(-σ)) := by
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity)]
    simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  rw [ht,restorationError,ENNReal.ofReal_mul hw]
  apply mul_le_mul' le_rfl
  apply (add_le_add hD (add_le_add (add_le_add (h₁.trans (class_discard_numeric N k₁ lam))
    (h₂.trans (class_discard_numeric N k₂ lam))) le_rfl)).trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end Falconer

end OAI
