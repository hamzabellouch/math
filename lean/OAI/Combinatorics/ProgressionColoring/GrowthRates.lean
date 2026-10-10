import OAI.Combinatorics.ProgressionColoring.Growth
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

namespace OAI

universe uIndex

namespace QuantitativeVanDerWaerden

open Filter

/-- The main real-power lower bound implies a rate uniform in the number
of colors. The color-dependent integer logarithm is estimated explicitly. -/
theorem log_ratio_lower_of_rpow_bound {A c : ℝ} {r k : ℕ}
    (hc : 0 ≤ c) (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hbound : (k : ℝ) ^ (c * k * (Nat.log 2 r : ℝ)) < A) :
    (c / (2 * Real.log 2)) * Real.log (k : ℝ) ≤
      Real.log A / ((k : ℝ) * Real.log (r : ℝ)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hrone : (1 : ℝ) < r := by exact_mod_cast (by omega : 1 < r)
  have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos hrone
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hlogs := Real.log_lt_log (Real.rpow_pos_of_pos hkpos _) hbound
  rw [Real.log_rpow hkpos] at hlogs
  have hmul :
      c * (k : ℝ) * (Real.log (r : ℝ) / (2 * Real.log 2)) * Real.log (k : ℝ) ≤
        c * (k : ℝ) * (Nat.log 2 r : ℝ) * Real.log (k : ℝ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (log_div_two_log_two_le_natLog hr)
        (mul_nonneg hc hkpos.le)) hlogk
  have hden : 0 < (k : ℝ) * Real.log (r : ℝ) := mul_pos hkpos hlogr
  calc
    (c / (2 * Real.log 2)) * Real.log (k : ℝ) =
        (c * (k : ℝ) * (Real.log (r : ℝ) / (2 * Real.log 2)) *
          Real.log (k : ℝ)) / ((k : ℝ) * Real.log (r : ℝ)) := by
      field_simp
    _ ≤ (c * (k : ℝ) * (Nat.log 2 r : ℝ) * Real.log (k : ℝ)) /
        ((k : ℝ) * Real.log (r : ℝ)) :=
      div_le_div_of_nonneg_right hmul hden.le
    _ ≤ Real.log A / ((k : ℝ) * Real.log (r : ℝ)) :=
      div_le_div_of_nonneg_right hlogs.le hden.le

/-- The large-color exponential lower bound gives a rate independent of
the progression length. -/
theorem log_ratio_lower_of_exp_bound {A r : ℝ} (hr : 1 < r)
    (hbound : Real.exp ((Real.log r) ^ 2 / (64 * Real.log 2)) < A) :
    Real.log r / (64 * Real.log 2) ≤ Real.log A / Real.log r := by
  have hlogr : 0 < Real.log r := Real.log_pos hr
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogs := Real.log_lt_log (Real.exp_pos _) hbound
  rw [Real.log_exp] at hlogs
  apply (le_div_iff₀ hlogr).2
  calc
    (Real.log r / (64 * Real.log 2)) * Real.log r =
        (Real.log r) ^ 2 / (64 * Real.log 2) := by ring
    _ ≤ Real.log A := hlogs.le

/-- A common eventual lower bound proves divergence of the actual real
infima. Nonemptiness is explicit; the common lower bound supplies the
lower-boundedness required by conditional completeness. -/
theorem tendsto_iInf_atTop_of_uniform_lower {ι : Type uIndex} [Nonempty ι]
    {F : ℕ → ι → ℝ} {g : ℕ → ℝ}
    (hg : Tendsto g atTop atTop)
    (h : ∀ᶠ n : ℕ in atTop, ∀ i, g n ≤ F n i) :
    Tendsto (fun n => ⨅ i, F n i) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ hg
  exact h.mono (fun n hn => le_ciInf hn)

end QuantitativeVanDerWaerden

end OAI
