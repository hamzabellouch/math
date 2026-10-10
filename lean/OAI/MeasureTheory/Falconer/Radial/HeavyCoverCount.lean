import OAI.MeasureTheory.Falconer.Estimates.EndpointDyadicScale

namespace OAI

/-! # Absorbing the fixed heavy-cover constant into the angular power margin -/

namespace Falconer
open Filter
open scoped ENNReal Topology

theorem heavy_cover_card_le {m : ℕ} {F K T : ℝ} (hF : 0 < F) (hK : 0 ≤ K)
    (h : (m:ℝ≥0∞)*ENNReal.ofReal F ≤ ENNReal.ofReal K) (hbudget : K ≤ T*F) :
    (m:ℝ) ≤ T := by
  have hm : ENNReal.ofReal ((m:ℝ)*F) ≤ ENNReal.ofReal K := by
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg m),ENNReal.ofReal_natCast] using h
  have hm' := (ENNReal.ofReal_le_ofReal_iff hK).mp hm
  nlinarith

theorem eventually_heavy_cover_card {q b K : ℝ} (hb : 0 < b) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ m : ℕ,
      (m:ℝ≥0∞)*ENNReal.ofReal ((1/(2:ℝ)^N)^(q+b/2)) ≤ ENNReal.ofReal K →
      (m:ℝ) ≤ (1/(2:ℝ)^N)^(-q-b) := by
  have he := eventually_const_mul_rpow_lt (show -b/2 < (0:ℝ) by linarith) K
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (dyadic_inverse_tendsto.eventually he)
  refine ⟨N₀,fun N hN m hm => ?_⟩
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  apply heavy_cover_card_le (Real.rpow_pos_of_pos hδ _) hK hm
  have hbound : K ≤ (1/(2:ℝ)^N)^(-b/2) := by
    have hh := (hN₀ N hN).2
    simpa only [Real.rpow_zero,mul_one] using hh.le
  apply hbound.trans_eq
  rw [← Real.rpow_add hδ]
  congr 1
  ring

end Falconer

end OAI
