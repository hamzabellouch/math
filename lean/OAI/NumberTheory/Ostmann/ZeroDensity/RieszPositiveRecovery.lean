import OAI.NumberTheory.Ostmann.ZeroDensity.RieszUnsmoothing

namespace OAI

/-! # Positive finite differences recover the sharp arithmetic count -/

namespace Ostmann

open scoped BigOperators

theorem finiteRieszSum_recover (S : Finset ℕ) (w : ℕ → ℝ) (x h m D : ℝ)
    (hh : 0 < h) (hw : ∀ n ∈ S, 0 ≤ w n)
    (hplus : finiteRieszSum S w (x + h) - finiteRieszSum S w x ≤ h * m + D)
    (hminus : h * m - D ≤ finiteRieszSum S w x - finiteRieszSum S w (x - h)) :
    |(∑ n ∈ S.filter (fun n : ℕ => (n : ℝ) ≤ x), w n) - m| ≤ D / h := by
  have hupper := (finiteRieszSum_step S w x h hh.le hw).1
  have hlower := (finiteRieszSum_step S w (x - h) h hh.le hw).2
  rw [sub_add_cancel] at hlower
  have habs : |h * ((∑ n ∈ S.filter (fun n : ℕ => (n : ℝ) ≤ x), w n) - m)| ≤ D := by
    rw [abs_le]
    constructor <;> nlinarith
  rw [abs_mul, abs_of_pos hh] at habs
  exact (le_div_iff₀ hh).mpr (by nlinarith)

theorem finiteRieszSum_quadratic_recovery (S : Finset ℕ) (w : ℕ → ℝ) (x h E : ℝ)
    (hh : 0 < h) (hw : ∀ n ∈ S, 0 ≤ w n)
    (hzero : |finiteRieszSum S w x - x ^ 2 / 2| ≤ E)
    (hplus : |finiteRieszSum S w (x + h) - (x + h) ^ 2 / 2| ≤ E)
    (hminus : |finiteRieszSum S w (x - h) - (x - h) ^ 2 / 2| ≤ E) :
    |(∑ n ∈ S.filter (fun n : ℕ => (n : ℝ) ≤ x), w n) - x| ≤ h / 2 + 2 * E / h := by
  have hb := finiteRieszSum_recover S w x h x (h ^ 2 / 2 + 2 * E) hh hw
    (by have ha := (abs_le.mp hplus).2; have hc := (abs_le.mp hzero).1; nlinarith)
    (by have ha := (abs_le.mp hminus).2; have hc := (abs_le.mp hzero).1; nlinarith)
  convert hb using 1
  field_simp

end Ostmann

end OAI
