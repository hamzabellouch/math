import OAI.MeasureTheory.Falconer.Slicing.SliceThreeTubeMass
import OAI.MeasureTheory.Falconer.Estimates.EndpointCountBudget

namespace OAI

/-! # A transverse original triple cannot carry too much common slice incidence -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem endpoint_slice_obstruction (μ : Measure (Space d))
    (V : Submodule ℝ (Space d)) (e : V ≃ₗᵢ[ℝ] Space 3)
    (w : Fin 3 → Sphere d) {η δ a κ C s : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hη : η < 1) (hband : ∀ i, w i ∈ directionSliceBand V η)
    (hgram : 2*δ^a ≤ Real.sqrt ((Matrix.gram ℝ (fun i => (w i : Space d))).det))
    (herror : 72*η ≤ 3*(δ^a)^2)
    (hbudget : (δ^(-1-κ))^3*((6*C+35)/δ^a)^6*(δ^(-κ)*(6*δ)^s)^2 < (δ^κ)^2)
    (E : Set (Space d)) (A : Fin 3 → Finset (Space d)) (R : ℝ)
    (hE : ∀ x ∈ E, ‖x‖ ≤ R)
    (hball : ∀ p : Space 3, μ {x | dist (e (V.orthogonalProjectionOnto x)) p < 6*δ} ≤
      ENNReal.ofReal (δ^(-κ)*(6*δ)^s))
    (hcover : ∀ i : Fin 3, ∀ x ∈ E, ∃ b ∈ A i,
      ‖perpendicularPart (w i : Space d) (x-b)‖ ≤ C*δ)
    (hcard : ∀ i, ((A i).card:ℝ) ≤ δ^(-1-κ))
    (hmass : δ^κ ≤ (μ E).toReal) : False := by
  have hΔ : 0 < δ^a := Real.rpow_pos_of_pos hδ a
  have hΔ1 : δ^a ≤ 1 := Real.rpow_le_one hδ.le hδ1 ha
  have hm := slice_three_tube_mass_sq μ V e w hη hband hΔ hΔ1 hgram herror
    E A R hE hδ hC (Real.rpow_nonneg hδ.le _) hball hcover
  have hc : ((A 0).card:ℝ)*((A 1).card:ℝ)*((A 2).card:ℝ) ≤ (δ^(-1-κ))^3 := by
    calc
      _ ≤ δ^(-1-κ)*δ^(-1-κ)*δ^(-1-κ) := by gcongr <;> apply hcard
      _ = _ := by ring
  have hup : (μ E).toReal^2 ≤
      (δ^(-1-κ))^3*((6*C+35)/δ^a)^6*(δ^(-κ)*(6*δ)^s)^2 := by
    apply hm.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
  have hlo := pow_le_pow_left₀ (Real.rpow_nonneg hδ.le κ) hmass 2
  exact (not_lt_of_ge (hlo.trans hup)) hbudget

end Falconer

end OAI
