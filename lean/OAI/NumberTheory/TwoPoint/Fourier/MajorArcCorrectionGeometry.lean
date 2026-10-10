import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNestedQuotients
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingOuterScale

namespace OAI

/-! Numerical conditions for the actual nested correction and character
windows, including the initial-block boundary and both floor errors. -/
namespace TwoPointCorrelations

open Finset

lemma major_arc_correction_outer {X V K : ℕ} {W : ℝ}
    (hXV : X ≤ V) (hVX : V+1 ≤ 2*X)
    (hboundary : ∀ d : ℕ, 0 < d → d ≤ mrtCorrectionCutoff W →
      (2*(K:ℝ)+1)/(X/d+1:ℕ) ≤ (W^4)⁻¹) :
    ∀ d : ℕ, 0 < d → d ≤ mrtCorrectionCutoff W →
      V/d+1 ≤ 2*X ∧ (2*(K:ℝ)+1)/(V/d+1:ℕ) ≤ (W^4)⁻¹ := by
  intro d hd hdD
  refine ⟨(Nat.add_le_add_right (Nat.div_le_self V d) 1).trans hVX,?_⟩
  apply le_trans _ (hboundary d hd hdD)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact_mod_cast Nat.add_le_add_right (Nat.div_le_div_right hXV) 1

lemma major_arc_correction_window_data {H h K V q : ℕ} {W Q : ℝ}
    (hW : 2 ≤ W) (hH : W^252 ≤ (H:ℝ))
    (hh : (H:ℝ)/W^2 ≤ h) (hhH : h ≤ H) (hhV : h ≤ V)
    (hHK : H+2 ≤ K) (hQ : Q ≤ (H:ℝ)/W^3) (hq : 0 < q) (hqW : (q:ℝ) ≤ W) :
    W^250 ≤ (h:ℝ) ∧
    ∀ d : ℕ, 0 < d → d ≤ mrtCorrectionCutoff W →
      q ≤ V/d+1 ∧ ∀ k : ℕ, 1 ≤ k → k ≤ h/d+1 →
        ((h/d+1:ℕ):ℝ)/W^2 ≤ k → ∀ b ∈ q.divisors,
          4 ≤ k/b+1 ∧ k/b+1 ≤ K ∧ W ≤ (k/b+1:ℕ) ∧ Q/(k/b+1:ℕ) ≤ W^7 := by
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  have hH0 : 0 ≤ (H:ℝ) := Nat.cast_nonneg H
  have hbase : W^250 ≤ (H:ℝ) :=
    (pow_le_pow_right₀ hW1 (by norm_num : (250:ℕ)≤252)).trans hH
  have hlarge : W^250 ≤ (h:ℝ) := by
    apply le_trans _ hh
    apply (le_div_iff₀ (pow_pos hW0 2)).mpr
    simpa only [←pow_add] using hH
  refine ⟨hlarge,?_⟩
  intro d hd hdD
  have hdW : (d:ℝ) ≤ W^5 :=
    (show (d:ℝ) ≤ mrtCorrectionCutoff W by exact_mod_cast hdD).trans
      (mrt_correction_cutoff_bounds hW).2.2
  have hqV : q ≤ V/d+1 := by
    have hlen := mrt_correction_quotient_power hW1 hbase hd hdW hh
    have hsmall : (q:ℝ) ≤ W^243 := hqW.trans (le_self_pow₀ hW1 (by decide))
    have hqhd : q ≤ h/d+1 := by exact_mod_cast hsmall.trans hlen
    exact hqhd.trans (Nat.add_le_add_right (Nat.div_le_div_right hhV) 1)
  refine ⟨hqV,?_⟩
  intro k _ hkh hkl b hb
  have hb0 : 0 < b := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hb).1 hq
  have hbW : (b:ℝ) ≤ W :=
    (show (b:ℝ) ≤ q by exact_mod_cast Nat.le_of_dvd hq (Nat.mem_divisors.mp hb).1).trans hqW
  have hlen := mrt_nested_prefix_large hW1 hbase hd hb0 hdW hbW hh hkl
  have hWlen : W ≤ (k/b+1:ℕ) := (le_self_pow₀ hW1 (by decide : (240:ℕ)≠0)).trans hlen
  have hfour : 4 ≤ (k/b+1:ℕ) := by
    have hfourpow : (4:ℝ) ≤ W^240 := by
      have hs : (4:ℝ) ≤ W^2 := by nlinarith
      exact hs.trans (pow_le_pow_right₀ hW1 (by norm_num : (2:ℕ)≤240))
    exact_mod_cast hfourpow.trans hlen
  exact ⟨hfour,(mrt_nested_prefix_upper hhH hkh).trans hHK,hWlen,
    mrt_nested_prefix_prime_ratio hW0 hH0 hQ hd hb0 hdW hbW hh hkl⟩

end TwoPointCorrelations

end OAI
