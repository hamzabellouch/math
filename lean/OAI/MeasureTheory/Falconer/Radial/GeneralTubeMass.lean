import OAI.MeasureTheory.Falconer.Estimates.GeneralTransverseCount
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # A mass bound for an actual intersection of transverse tube families -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal BigOperators
variable {n : ℕ}

theorem general_tube_mass_power (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (μ : Measure (Space (n+1)))
    (v : Fin (n+1) → Space (n+1)) (hv : ∀ i, ‖v i‖ = 1)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hgram : Δ ≤ Real.sqrt (Matrix.gram ℝ v).det)
    (E : Set (Space (n+1))) (A : Fin (n+1) → Finset (Space (n+1))) (R : ℝ)
    (hE : ∀ x ∈ E, ‖x‖ ≤ R) {δ C H : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hball : ∀ p : Space (n+1), μ (ball p ((((n+1:ℕ):ℝ)^2+1)*δ)) ≤ ENNReal.ofReal H)
    (hcover : ∀ i : Fin (n+1), ∀ x ∈ E, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (x-a)‖ ≤ C*δ) :
    (μ E).toReal^n ≤ (∏ i : Fin (n+1), ((A i).card:ℝ))*
      (generalTubeCountConstant (n+1) C/Δ)^(n*(n+1))*H^n := by
  obtain ⟨P,hP,hcard⟩ := general_transverse_tube_cover hLW hn v hv hΔ hΔ1 hgram E A R hE hδ hC hcover
  have hm : μ E ≤ ENNReal.ofReal ((P.card:ℝ)*H) := by
    calc
      _ ≤ μ (⋃ p ∈ P, ball p ((((n+1:ℕ):ℝ)^2+1)*δ)) := by
        apply measure_mono
        intro x hx
        obtain ⟨p,hp,hd⟩ := hP x hx
        exact mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨hp,by change dist x p < _; nlinarith⟩⟩
      _ ≤ ∑ p ∈ P, μ (ball p ((((n+1:ℕ):ℝ)^2+1)*δ)) := measure_biUnion_finset_le P _
      _ ≤ ∑ _p ∈ P, ENNReal.ofReal H := Finset.sum_le_sum (fun p _ => hball p)
      _ = (P.card:ℝ≥0∞)*ENNReal.ofReal H := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ = _ := by rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) hH)] at hreal
  calc
    _ ≤ ((P.card:ℝ)*H)^n := pow_le_pow_left₀ ENNReal.toReal_nonneg hreal n
    _ = (P.card:ℝ)^n*H^n := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (pow_nonneg hH n)

end Falconer

end OAI
