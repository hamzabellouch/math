import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! # Relative square-root errors -/

namespace KadisonKastler

theorem relative_sqrt_sub_bound {s t ε : ℝ} (hs : 0 ≤ s) (ht : 0 < t)
    (h : |s-t| ≤ ε*t) :
    |Real.sqrt s-Real.sqrt t| ≤ ε*Real.sqrt t := by
  have htroot := Real.sqrt_pos.mpr ht
  have hsroot := Real.sqrt_nonneg s
  have hsquare := Real.sq_sqrt hs
  have htsquare := Real.sq_sqrt ht.le
  have hfactor : |Real.sqrt s-Real.sqrt t| * (Real.sqrt s+Real.sqrt t) = |s-t| := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt s+Real.sqrt t), ← abs_mul]
    congr 1
    nlinarith
  have hle : |Real.sqrt s-Real.sqrt t| * Real.sqrt t ≤ ε*t :=
    (mul_le_mul_of_nonneg_left (by linarith : Real.sqrt t ≤ Real.sqrt s+Real.sqrt t)
      (abs_nonneg _)).trans (hfactor.le.trans h)
  have he : ε*t = (ε*Real.sqrt t)*Real.sqrt t := by rw [mul_assoc, ← pow_two, htsquare]
  rw [he] at hle
  exact (mul_le_mul_iff_left₀ htroot).mp hle

end KadisonKastler

end OAI
