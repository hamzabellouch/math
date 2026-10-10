import OAI.MeasureTheory.Falconer.Estimates.TransversePhysicalCount

namespace OAI

/-! # Frostman mass obstruction for three transverse tube families -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem three_tube_frostman_mass_sq (μ : Measure (Space 3))
    (v : Fin 3 → Space 3) (hv : ∀ i, ‖v i‖ = 1)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hgram : Δ ≤ Real.sqrt (tripleGram (v 0) (v 1) (v 2)))
    (E : Set (Space 3)) (A : Fin 3 → Finset (Space 3)) (R : ℝ)
    (hE : ∀ x ∈ E, ‖x‖ ≤ R) {δ C H f : ℝ} (hδ : 0 < δ)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hball : ∀ p : Space 3, μ (ball p (6*δ)) ≤ ENNReal.ofReal (H*(6*δ)^f))
    (hcover : ∀ i : Fin 3, ∀ x ∈ E, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (x-a)‖ ≤ C*δ) :
    (μ E).toReal^2 ≤ ((A 0).card:ℝ)*((A 1).card:ℝ)*((A 2).card:ℝ)*
      ((6*C+35)/Δ)^6*(H*(6*δ)^f)^2 := by
  obtain ⟨P,hP,hcard⟩ := three_transverse_tube_cover v hv hΔ hΔ1 hgram E A R hE hδ hC hcover
  have hB : 0 ≤ H*(6*δ)^f := by positivity
  have hmass : μ E ≤ ENNReal.ofReal ((P.card:ℝ)*(H*(6*δ)^f)) := by
    calc
      _ ≤ μ (⋃ p ∈ P, ball p (6*δ)) := by
        apply measure_mono
        intro x hx
        obtain ⟨p,hp,hd⟩ := hP x hx
        exact mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨hp,by change dist x p < 6*δ; linarith⟩⟩
      _ ≤ ∑ p ∈ P, μ (ball p (6*δ)) := measure_biUnion_finset_le P _
      _ ≤ ∑ _p ∈ P, ENNReal.ofReal (H*(6*δ)^f) := Finset.sum_le_sum (fun p _ => hball p)
      _ = (P.card:ℝ≥0∞)*ENNReal.ofReal (H*(6*δ)^f) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ = _ := by rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) hB)] at hreal
  calc
    _ ≤ ((P.card:ℝ)*(H*(6*δ)^f))^2 := pow_le_pow_left₀ ENNReal.toReal_nonneg hreal 2
    _ = (P.card:ℝ)^2*(H*(6*δ)^f)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)

end Falconer

end OAI
