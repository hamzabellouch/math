import OAI.NumberTheory.Ostmann.Supply.UniformNorms

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

theorem balanced_nonempty (S : Finset (ZMod p)) (hlo : (1/3:ℝ) ≤ density S) :
    S.Nonempty := by
  by_contra h
  have hz : S.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
  norm_num [density,hz] at hlo

theorem balanced_compl (S : Finset (ZMod p))
    (hlo : (1/3:ℝ) ≤ density S) (hhi : density S ≤ 2/3) :
    (1/3:ℝ) ≤ density Sᶜ ∧ density Sᶜ ≤ 2/3 := by
  rw [density_compl]
  constructor <;> linarith

theorem balanced_uniform_norm_sq (S : Finset (ZMod p))
    (hlo : (1/3:ℝ) ≤ density S) : ‖uniformVector S‖^2 ≤ 3/(p:ℝ) := by
  have hp : (0:ℝ)<p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have hs : (0:ℝ)<S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr (balanced_nonempty S hlo))
  rw [uniformVector_norm_sq S (balanced_nonempty S hlo),inv_eq_one_div]
  apply (div_le_div_iff₀ hs hp).mpr
  have h := (le_div_iff₀ hp).mp (by simpa only [density,ZMod.card] using hlo)
  linarith

theorem balanced_uniform_norm (S : Finset (ZMod p))
    (hlo : (1/3:ℝ) ≤ density S) : ‖uniformVector S‖ ≤ 2/Real.sqrt p := by
  have hp : (0:ℝ)<p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have hr : 0<Real.sqrt (p:ℝ) := Real.sqrt_pos.mpr hp
  have h := (le_div_iff₀ hp).mp (balanced_uniform_norm_sq S hlo)
  apply (le_div_iff₀ hr).mpr
  have hs := Real.sq_sqrt hp.le
  have hh : (‖uniformVector S‖*Real.sqrt p)^2 ≤ 3 := by nlinarith
  nlinarith [mul_nonneg (norm_nonneg (uniformVector S)) hr.le]

theorem balanced_uniformCoefficient_error (S : Finset (ZMod p))
    (hlo : (1/3:ℝ) ≤ density S) (hhi : density S ≤ 2/3)
    {ε : ℝ} (hε : 0 ≤ ε) :
    uniformCoefficient S*(ε*Real.sqrt p) ≤ 2*ε/Real.sqrt p := by
  have hp : (0:ℝ)<p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have hr : (Real.sqrt (p:ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have h := mul_le_mul_of_nonneg_right (uniformCoefficient_le S hlo hhi)
    (mul_nonneg hε (Real.sqrt_nonneg (p:ℝ)))
  have he : (2/(p:ℝ))*(ε*Real.sqrt p) = 2*ε/Real.sqrt p := by
    have hs := Real.sq_sqrt hp.le
    field_simp
    nlinarith
  exact h.trans_eq he

end Ostmann.Supply

end

end OAI
