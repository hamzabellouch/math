import OAI.NumberTheory.TotientAsymptotic.ExceptionalValueCount

namespace OAI

/-! A concrete cutoff between the fourth-root and square-root scales. -/
noncomputable section
namespace TotientAsymptotic

lemma sqrt_counting_cutoff {x : ℝ} (hx : 256 ≤ x) :
    4 ≤ ⌊Real.sqrt x⌋₊ ∧ ((⌊Real.sqrt x⌋₊:ℝ)^2 ≤ x) ∧
      x^(1/4:ℝ) ≤ (⌊Real.sqrt x⌋₊:ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hy16 : 16 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith : (16:ℝ)^2 ≤ x)
  have hy0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hn : 4 ≤ ⌊Real.sqrt x⌋₊ := Nat.le_floor (show (4:ℝ) ≤ Real.sqrt x by linarith)
  have hs : (⌊Real.sqrt x⌋₊:ℝ)^2 ≤ x := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg ⌊Real.sqrt x⌋₊) (Nat.floor_le hy0) 2
    rwa [Real.sq_sqrt hx0] at hh
  have hroot : x^(1/4:ℝ)=Real.sqrt (Real.sqrt x) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hx0]
    norm_num
  have hhalf : Real.sqrt (Real.sqrt x) ≤ Real.sqrt x/2 := by
    apply (Real.sqrt_le_iff).mpr ⟨by positivity,?_⟩
    nlinarith only [hy16]
  have hf : Real.sqrt x/2 ≤ (⌊Real.sqrt x⌋₊:ℝ) := by
    linarith [Nat.sub_one_lt_floor (Real.sqrt x)]
  exact ⟨hn,hs,hroot ▸ hhalf.trans hf⟩

end TotientAsymptotic

end

end OAI
