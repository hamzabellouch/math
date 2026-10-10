import OAI.Analysis.Laughlin.Pair.Conjugation

namespace OAI

namespace Laughlin

theorem modeFactor_nonneg (Q x : ℕ) : 0 ≤ modeFactor Q x := Real.sqrt_nonneg _

theorem modeFactor_le_one (Q x : ℕ) (hQ : 0 < Q) : modeFactor Q x ≤ 1 := by
  have hpow : (0 : ℝ) < (Q : ℝ)^x := pow_pos (by exact_mod_cast hQ) _
  have hd : (Q.descFactorial x : ℝ) ≤ (Q : ℝ)^x := by
    exact_mod_cast Nat.descFactorial_le_pow Q x
  have h := Real.sqrt_le_sqrt ((div_le_one hpow).mpr hd)
  simpa [modeFactor] using h

theorem pairFactor_one_le (Q p : ℕ) (hp : p ≤ 2*Q-2) : 1 ≤ pairFactor Q p := by
  have hd : (0 : ℝ) < (2*Q-2).descFactorial p := by exact_mod_cast Nat.descFactorial_pos.mpr hp
  have hn : (2*Q-2).descFactorial p ≤ (2*Q)^p := by
    apply (Nat.descFactorial_le_pow (2*Q-2) p).trans
    exact Nat.pow_le_pow_left (Nat.sub_le _ _) p
  have hr : ((2*Q-2).descFactorial p : ℝ) ≤ ((2 : ℝ)*Q)^p := by exact_mod_cast hn
  have h := Real.sqrt_le_sqrt ((one_le_div hd).mpr hr)
  simpa [pairFactor] using h

end Laughlin

end OAI
