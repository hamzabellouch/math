import OAI.Analysis.LipschitzHilbert.Trees.ResidualBudget

namespace OAI

/-! The common residual coefficient bound is polynomial in the source
parameter. Its exponent is fixed before selecting the mass cutoff. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_source_residual_weight_budget (Cmass : ℝ) (hCmass : 0 ≤ Cmass) :
    ∀ᶠ L : ℝ in atTop, ∀ (a Z Nmass nroot : ℝ) (K : ℕ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (K:ℝ) ≤ L^2 →
      0 < Nmass → Real.log Nmass ≤ 2*L → 1 ≤ nroot → nroot ≤ L^Cmass*Nmass →
      1+(a+Z*K)*Real.log nroot ≤ L^6 := by
  filter_upwards [eventually_ge_atTop (max 1 (3*(Cmass+2)+1))] with L hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hlarge : 3*(Cmass+2)+1 ≤ L := (le_max_right _ _).trans hL
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  intro a Z Nmass nroot K _ha0 ha1 hZ0 hZ hK hN hlogN hn1 hn
  have hn0 : 0 < nroot := zero_lt_one.trans_le hn1
  have hlogpos : 0 ≤ Real.log nroot := Real.log_nonneg hn1
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)
  have hlog : Real.log nroot ≤ (Cmass+2)*L := by
    calc
      _ ≤ Real.log (L^Cmass*Nmass) := Real.log_le_log hn0 hn
      _ = Cmass*Real.log L+Real.log Nmass := by
        rw [Real.log_mul (Real.rpow_pos_of_pos hLpos _).ne' hN.ne',Real.log_rpow hLpos]
      _ ≤ Cmass*L+2*L := add_le_add (mul_le_mul_of_nonneg_left hlogL hCmass) hlogN
      _ = _ := by ring
  have hpow4 : 1 ≤ L^4 := one_le_pow₀ hL1
  have hZK : Z*K ≤ 2*L^4 := by
    calc
      _ ≤ (2*L^2)*L^2 := mul_le_mul hZ hK (Nat.cast_nonneg K) (by positivity)
      _ = _ := by ring
  have hc : a+Z*K ≤ 3*L^4 := by linarith
  have hmain : (a+Z*K)*Real.log nroot ≤ (3*L^4)*((Cmass+2)*L) :=
    mul_le_mul hc hlog hlogpos (by positivity)
  have hpow5 : 1 ≤ L^5 := one_le_pow₀ hL1
  calc
    _ ≤ 1+(3*L^4)*((Cmass+2)*L) := add_le_add le_rfl hmain
    _ = 1+(3*(Cmass+2))*L^5 := by ring
    _ ≤ (1+3*(Cmass+2))*L^5 := by nlinarith
    _ ≤ L*L^5 := mul_le_mul_of_nonneg_right (by linarith : 1+3*(Cmass+2) ≤ L)
      (by positivity)
    _ = L^6 := by ring

end LipschitzHilbert

end

end OAI
