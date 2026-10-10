import OAI.MeasureTheory.Falconer.Estimates.EndpointPowerAbsorption

namespace OAI

/-! # The common-triple mass and bad-triple thresholds are compatible -/

namespace Falconer
open Real Filter
open scoped Topology

theorem endpoint_common_mass_ratio {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    (δ^(2*u))^3/(2*(δ^(-6*u))^5) = (1/2)*δ^(36*u) := by
  have hp : (δ^(2*u))^3 = δ^(6*u) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
    congr 1
    ring
  have hq : (δ^(-6*u))^5 = δ^(-30*u) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
    congr 1
    ring
  rw [hp,hq]
  calc
    _ = (1/2)*(δ^(6*u)/δ^(-30*u)) := by ring
    _ = _ := by rw [← Real.rpow_sub hδ]; congr 2; ring

theorem endpoint_bad_mass_ratio {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    (δ^(2*u))^3/(4*(δ^(-6*u))^3) = (1/4)*δ^(24*u) := by
  have hp : (δ^(2*u))^3 = δ^(6*u) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
    congr 1
    ring
  have hq : (δ^(-6*u))^3 = δ^(-18*u) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
    congr 1
    ring
  rw [hp,hq]
  calc
    _ = (1/4)*(δ^(6*u)/δ^(-18*u)) := by ring
    _ = _ := by rw [← Real.rpow_sub hδ]; congr 2; ring

theorem eventually_endpoint_mass_thresholds {u τ : ℝ}
    (hu : 0 < u) (hτ : 30*u < τ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧
      δ^(40*u) ≤ (δ^(2*u))^3/(2*(δ^(-6*u))^5) ∧
      δ^τ+2*δ^(-6*u)*δ^τ ≤ (δ^(2*u))^3/(4*(δ^(-6*u))^3) := by
  have hb := eventually_const_mul_rpow_lt (show 24*u < τ-6*u by linarith) 12
  have hm := eventually_const_mul_rpow_lt (show 36*u < 40*u by linarith) 2
  filter_upwards [hb,hm,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hb hm hδ
  refine ⟨hδ.1,?_,?_⟩
  · rw [endpoint_common_mass_ratio hδ.1]
    linarith [hm.2]
  · rw [endpoint_bad_mass_ratio hδ.1]
    have hM : 1 ≤ δ^(-6*u) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ.1 hδ.2 (by linarith)
    have hh : δ^τ+2*δ^(-6*u)*δ^τ ≤ 3*δ^(-6*u)*δ^τ := by
      nlinarith [mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hδ.1.le τ)]
    have he : δ^(-6*u)*δ^τ = δ^(τ-6*u) := by rw [← Real.rpow_add hδ.1]; congr 1; ring
    rw [mul_assoc,he] at hh
    linarith [hb.2]

end Falconer

end OAI
