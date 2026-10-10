import OAI.NumberTheory.TwoPoint.Bounds.RoughFourierSieve
import OAI.NumberTheory.TwoPoint.Bounds.RoughShiftEndpoints

namespace OAI

/-! The complete quantitative rough-shift analytic estimate, conditional
only on the stated published Mertens and MRT inputs. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

/-- Manuscript `(q:rough-shifts)`, including arbitrary (possibly nonunit)
progression classes. The finite rough set is unrestricted within its interval. -/
theorem rough_liouville_shifts (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) (h : ℕ) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop, ∀ Y D l : ℕ,
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (2 * L) →
      Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ Y →
      ∀ [NeZero l] (a : ZMod l) (Z : Finset ℕ),
      (∀ z ∈ Z, D ≤ z ∧ z < D + D ∧
        avoidsPrimeSet (sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ)))) z) →
      ‖roughShiftAverage (progressionSequence liouville l a) liouville Z h Y‖ ≤
        C * L ^ (-21 / 20 : ℝ) := by
  obtain ⟨U, V, hU, hV, hFourier⟩ := hM.rough_fourier
  obtain ⟨K, hK, hWindow⟩ := hMRT.progression_window_scale
  let C := 2 * U + (2 * (h : ℝ) + 1) + (2 * (h : ℝ) + 1) * U * V * K
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hFourier, hWindow, eventually_rough_interval_lower,
    eventually_ge_atTop 10] with L hFourierL hWindowL hLowerL hL
  intro Y D l hDlower hDupper hYlower _ a Z hZ
  have hL₁ : 1 ≤ L := by linarith
  have hD₁₀ : 10 ≤ D := hLowerL D hDlower
  have hYp : (0 : ℝ) < Y := (Real.exp_pos _).trans_le hYlower
  have hYN : 0 < Y := by exact_mod_cast hYp
  have hratio := rough_shift_ratio L hL D Y hDupper hYlower
  have hrat₁ : (D : ℝ) / Y ≤ 1 := hratio.trans (by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hL₁ (show (-21 / 20 : ℝ) ≤ 0 by norm_num))
  have hDY : D ≤ Y := by exact_mod_cast (div_le_one hYp).mp hrat₁
  have hYplus : Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ (Y + 1 : ℕ) :=
    hYlower.trans (by exact_mod_cast Nat.le_succ Y)
  obtain ⟨hB, hFourth⟩ := hFourierL D h hDlower hh Z hZ
  exact rough_shift_power_bound (progressionSequence liouville l a) liouville
    (liouville_oneBounded.progressionSequence l a) liouville_oneBounded Z D h Y
    (by omega) hYN (fun z hz => by have := (hZ z hz).2.1; omega)
    L U V K hL₁ hU.le hV.le hK.le hratio hB hFourth
    (fun θ => hWindowL Y D l (by omega) hD₁₀ (by omega)
      hDlower hDupper hYplus a θ)

end TwoPointCorrelations

end OAI
