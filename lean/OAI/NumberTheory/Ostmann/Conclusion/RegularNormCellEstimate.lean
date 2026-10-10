import OAI.NumberTheory.Ostmann.Conclusion.RegularNormCellBounds
import OAI.NumberTheory.Ostmann.Conclusion.RegularNormGeneral

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open scoped BigOperators
open Ostmann.Arithmetic.PrimeCellReplacement Ostmann.Arithmetic.PrimeProgression
open Ostmann.Construction

theorem exists_regular_logCell_test_bound :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧
      ∀ c : ℝ, L₀+1 ≤ c → 2 ≤ c →
      ∀ (M : ℕ) [NeZero M] (hZ : 0 < logCellMass c ∅),
      (logCellMass c ∅)⁻¹ ≤ 2*c → (M : ℝ)/(M.totient : ℝ) ≤ 2 →
      (M : ℝ) ≤ Real.exp (d*(c-1)^(1/3 : ℝ)) →
      2*K*c*M*Real.exp (-d*(c-1)^(1/3 : ℝ)) ≤ 1 →
      ∀ F : (ZMod M)ˣ → ℝ, (∀ u, 0 ≤ F u) → (∑ u, F u) ≤ (M : ℝ) →
      (logCellPrior c ∅ hZ).mean (fun p => unitTest F ((p : ℕ) : ZMod M)) ≤ 18 := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,hAP⟩ := exists_positiveUnitTest_primeCell_upper_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro c hc hc2 M _ hZ hZinv hratio hmod herror F hF hsum
  have hcell (lo hi : ℝ) (hlo : c-1 ≤ lo) (horder : lo ≤ hi)
      (hwidth : hi-lo ≤ 1) (hhi : hi ≤ c+1) :
      realTestSum ⌈Real.exp (c+1)⌉₊ M lo hi (logCellMass c ∅) F ≤ 9 := by
    have hpow : (c-1)^(1/3 : ℝ) ≤ lo^(1/3 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hlo (by norm_num)
    have hmod' : (M : ℝ) ≤ Real.exp (d*lo^(1/3 : ℝ)) :=
      hmod.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpow hd.le))
    have hN : ⌊Real.exp hi⌋₊ ≤ ⌈Real.exp (c+1)⌉₊ :=
      (Nat.floor_mono (Real.exp_le_exp.mpr hhi)).trans (Nat.floor_le_ceil _)
    have hh := hAP lo hi (by linarith) horder hwidth ⌈Real.exp (c+1)⌉₊ M
      (logCellMass c ∅) hN hZ hmod' F M hF hsum
    have hmain := regular_cell_principal_le hc2 hZ hZinv hratio hlo horder hwidth
    have he : Real.exp (-d*lo^(1/3 : ℝ)) ≤ Real.exp (-d*(c-1)^(1/3 : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have herr : ((K/logCellMass c ∅)*Real.exp (-d*lo^(1/3 : ℝ)))*(M : ℝ) ≤ 1 := by
      calc
        _ ≤ (K*(2*c))*Real.exp (-d*(c-1)^(1/3 : ℝ))*(M : ℝ) := by
          rw [div_eq_mul_inv]
          gcongr
        _ = 2*K*c*M*Real.exp (-d*(c-1)^(1/3 : ℝ)) := by ring
        _ ≤ 1 := herror
    nlinarith
  have hmean := logCellPrior_nonnegative_test_le c hZ
    (fun p => unitTest F (p : ZMod M)) (fun p => unitTest_nonneg F hF _)
  change (logCellPrior c ∅ hZ).mean _ ≤
    realTestSum ⌈Real.exp (c+1)⌉₊ M (c-1) c (logCellMass c ∅) F+
    realTestSum ⌈Real.exp (c+1)⌉₊ M c (c+1) (logCellMass c ∅) F at hmean
  have hleft := hcell (c-1) c le_rfl (by linarith) (by linarith) (by linarith)
  have hright := hcell c (c+1) (by linarith) (by linarith) (by linarith) le_rfl
  linarith

end Ostmann.Conclusion

end

end OAI
