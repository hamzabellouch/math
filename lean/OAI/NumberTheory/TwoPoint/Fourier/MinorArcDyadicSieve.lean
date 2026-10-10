import OAI.NumberTheory.TwoPoint.Fourier.MinorArcCofactorCutoff

namespace OAI

/-! Cancellation of the dyadic cofactor scale in the fourth moment. -/

namespace TwoPointCorrelations

open Finset Filter

theorem minor_arc_dyadic_bilinear_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℕ in atTop,
      ∀ (P : Finset ℕ) (X H : ℕ), 1 ≤ H → H ≤ X → R ≤ X →
      (∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ R ≤ p ∧ p ≤ 2 * R) →
      ∀ (a c : ℕ → ℂ), (∀ m, ‖a m‖ ≤ 1) → (∀ p ∈ P, ‖c p‖ ≤ 1) →
      ∀ W : ℝ, 1 ≤ W → W ≤ (R : ℝ) → (R : ℝ) ≤ (H : ℝ) / W →
      ∀ (r : ℤ) (q : ℕ), 2 ≤ q → W ≤ (q : ℝ) → (q : ℝ) ≤ (H : ℝ) / W →
      ∀ α : ℝ, IsCoprime (q : ℤ) r →
      |α - (r : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      (∑ k ∈ range X, ‖minorArcBilinearWindow P ((X + H) / R + 1) H 1 a c α k‖) ^ 4 ≤
        C * (X : ℝ) ^ 4 * (H : ℝ) ^ 4 * (1 + Real.log (2 * (H : ℝ))) /
          (W * Real.log (R : ℝ) ^ 4) := by
  obtain ⟨C, hC, hbound⟩ := minor_arc_bilinear_sieve
  refine ⟨1728 * C, by positivity, ?_⟩
  have hb : ∀ᶠ R : ℕ in atTop, _ :=
    tendsto_natCast_atTop_atTop.eventually hbound
  filter_upwards [hb, eventually_ge_atTop 2] with R hbound hR
  intro P X H hH hHX hRX hP a c ha hc W hW hWR hRH r q hq hWq hqH α hcop happ
  have hR0 : 0 < R := by omega
  have hp : ∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ (R : ℝ) ≤ p ∧ p ≤ 2 * R := by
    intro p hp
    exact ⟨(hP p hp).1, (hP p hp).2.1, by exact_mod_cast (hP p hp).2.2.1,
      (hP p hp).2.2.2⟩
  have hbil := hbound P (2 * R) X ((X + H) / R + 1) H 1 (by norm_num) hp
    (by simp) a c (fun m _ => ha m) hc W hW hWR hRH
    r q hq hWq hqH α hcop happ
  have hlog : 0 ≤ 1 + Real.log (2 * (H : ℝ)) := by
    have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hh : 1 ≤ 2 * (H : ℝ) := by linarith
    linarith [Real.log_nonneg hh]
  have hK : 0 ≤ (1 + Real.log (2 * (H : ℝ))) / (W * Real.log (R : ℝ) ^ 4) :=
    div_nonneg hlog (mul_nonneg (by linarith) (by positivity))
  have hcore := mul_le_mul_of_nonneg_left
    (minor_arc_cofactor_total_bound X H R hR0 hRX hHX hH) hC.le
  have hfinal := mul_le_mul_of_nonneg_right hcore hK
  apply hbil.trans
  convert hfinal using 1 <;> ring

end TwoPointCorrelations

end OAI
