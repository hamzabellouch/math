import OAI.Combinatorics.ProgressionColoring.AffineEntropy

namespace OAI

/-!
# Entropy bound for a possibly empty finite signature set

The natural count may vanish. Taking its maximum with one lets the same
uniform entropy bound feed the sparse-perturbation budget in that case.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

/-- Natural signature counts obey the maximum-with-one entropy bound, including
the empty signature set. The finite counting premise is used unchanged. -/
theorem affine_nat_entropy_bound {k T : ℕ} (hk : 32 ≤ k)
    {G q A : ℝ} (hG : 1 ≤ G) (hq : 1 ≤ q) (hA : 0 ≤ A)
    (hcount : (T : ℝ) ≤ 25 * G *
      ((k : ℝ) * ((dimension k : ℝ) * q ^ 2 + 1) + 1) ^ 8)
    (hglobal : Real.log G ≤
      A * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log (k : ℝ))
    (hprime : Real.log q ≤
      4 * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log (k : ℝ)) :
    Real.log (max 1 (T : ℝ)) ≤
      (A + 108) * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log (k : ℝ) := by
  by_cases hT : T = 0
  · subst T
    have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
    simp only [Nat.cast_zero, max_eq_left (by norm_num : (0 : ℝ) ≤ 1), Real.log_one]
    positivity
  · have hTone : (1 : ℝ) ≤ T := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hT
    rw [max_eq_right hTone]
    exact affine_entropy_bound hk hTone hG hq hA hcount hglobal hprime

end QuantitativeVanDerWaerden.Parameters

end

end OAI
