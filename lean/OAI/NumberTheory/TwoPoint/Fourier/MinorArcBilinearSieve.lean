import OAI.NumberTheory.TwoPoint.Fourier.MinorArcBilinearWindow
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcSieveSaving

namespace OAI

/-! The prime sieve saving for the actual finite bilinear short-window sum. -/

namespace TwoPointCorrelations

open Finset Filter

theorem minor_arc_bilinear_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (P : Finset ℕ) (N X M H d : ℕ), 0 < d →
      (∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ R ≤ (p : ℝ) ∧ p ≤ N) → (N : ℝ) ≤ 2 * R →
      ∀ (a c : ℕ → ℂ), (∀ m ∈ range M, ‖a m‖ ≤ 1) → (∀ p ∈ P, ‖c p‖ ≤ 1) →
      ∀ W : ℝ, 1 ≤ W → W ≤ R → R ≤ (H : ℝ) / W →
      ∀ (r : ℤ) (q : ℕ), 2 ≤ q → W ≤ (q : ℝ) → (q : ℝ) ≤ (H : ℝ) / W →
      ∀ α : ℝ, IsCoprime (q : ℤ) r →
      |α - (r : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      (∑ k ∈ range X, ‖minorArcBilinearWindow P M H d a c α k‖) ^ 4 ≤
        C * (M : ℝ) ^ 3 * (X * (3 * H + 1) ^ 3 : ℕ) * H * R ^ 3 *
          (1 + Real.log (2 * (H : ℝ))) / (W * Real.log R ^ 4) := by
  obtain ⟨C, hC, hk⟩ := minor_arc_sieve_saving
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hk, eventually_ge_atTop (1 : ℝ)] with R hk hR
  intro P N X M H d hd hP hN a c ha hc W hW hWR hRH r q hq hWq hqH α hcop happ
  have hW0 : 0 < W := by linarith
  have hR0 : 0 < R := by linarith
  have hHR : R ≤ (H : ℝ) := by
    exact (le_mul_of_one_le_right hR0.le hW).trans ((le_div_iff₀ hW0).mp hRH)
  have hH0 : 0 ≤ (H : ℝ) := Nat.cast_nonneg H
  have hdouble : ∀ p ∈ P, 0 < p ∧ ∀ s ∈ P, s ≤ 2 * p := by
    intro p hp
    have hpR := (hP p hp).2.2.1
    constructor
    · have hp1 : (1 : ℝ) ≤ p := hR.trans hpR
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp1)
    · intro s hs
      have hsN : (s : ℝ) ≤ N := by exact_mod_cast (hP s hs).2.2.2
      have hsp : (s : ℝ) ≤ 2 * (p : ℝ) := by linarith
      exact_mod_cast hsp
  have hV : ∀ p ∈ P, (H : ℝ) / (d * p : ℕ) + 1 ≤ 2 * (H : ℝ) / R := by
    intro p hp
    have hpR := (hP p hp).2.2.1
    have hd1 : 1 ≤ d := hd
    have hdp : R ≤ ((d * p : ℕ) : ℝ) := by
      have hpdp : p ≤ d * p := by nlinarith
      exact hpR.trans (by exact_mod_cast hpdp)
    have hdiv : (H : ℝ) / (d * p : ℕ) ≤ (H : ℝ) / R :=
      div_le_div_of_nonneg_left hH0 hR0 hdp
    have hone : 1 ≤ (H : ℝ) / R := (le_div_iff₀ hR0).mpr (by simpa using hHR)
    calc
      _ ≤ (H : ℝ) / R + (H : ℝ) / R := add_le_add hdiv hone
      _ = _ := by ring
  have hbilinear := minor_arc_bilinear_fourth P X M H d hd hdouble a c ha hc α
    (2 * (H : ℝ) / R) hV
  have hHdiv : (H : ℝ) / W ≤ (2 * (H : ℝ)) / W := by gcongr; linarith
  have hkernel := hk P N (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1, (hP p hp).2.2.2⟩)
    hN (2 * (H : ℝ)) W (2 * (H : ℝ) / R) hW hWR r q hq hWq
    (hqH.trans hHdiv) (hRH.trans hHdiv) (by positivity) (le_refl _) α hcop happ
  have hfactor : 0 ≤ (M : ℝ) ^ 3 * (X * (3 * H + 1) ^ 3 : ℕ) := by positivity
  apply hbilinear.trans
  convert mul_le_mul_of_nonneg_left hkernel hfactor using 1
  ring

end TwoPointCorrelations

end OAI
