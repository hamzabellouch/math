import OAI.MeasureTheory.Falconer.Geometry.ScalarNormalizedLogBudget
import OAI.MeasureTheory.Falconer.Measures.ScalarDensityInverse

namespace OAI

/-! Eliminate the selected radius from the projection budget: its entire
 cost is controlled by logarithms of the original two weak constants. -/
namespace Falconer

noncomputable def scalarNormalizationRadius (κ K : ℝ) : ℕ := ⌈2*K^(1/κ)⌉₊

 theorem scalar_normalization_radius_log {κ K : ℝ} (hκ : 0 < κ) (hK : 1 ≤ K) :
    Real.log ((scalarNormalizationRadius κ K:ℝ)+10) ≤
      Real.log 13+(1/κ)*Real.log K := by
  have hpow : 1 ≤ K^(1/κ) := Real.one_le_rpow hK (by positivity)
  have hc := (Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 2*K^(1/κ))).le
  have hbound : (scalarNormalizationRadius κ K:ℝ)+10 ≤ 13*K^(1/κ) := by
    change (⌈2*K^(1/κ)⌉₊:ℝ)+10 ≤ _
    linarith
  have hl := Real.log_le_log (by positivity : (0:ℝ) < (scalarNormalizationRadius κ K:ℝ)+10) hbound
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_rpow (by linarith : 0 < K)] at hl
  exact hl

 theorem scalar_normalization_cost {κ : ℝ} (hκ : 0 < κ) :
    ∃ c p q : ℝ, 0 ≤ c ∧ 0 ≤ p ∧ 0 ≤ q ∧ ∀ Kcoef Kproj : ℝ,
      1 ≤ Kcoef → 1 ≤ Kproj →
      Real.log (scalarNormalizedProjectionBudget (scalarNormalizationRadius κ Kcoef) Kproj) ≤
        c+p*Real.log Kcoef+q*Real.log Kproj := by
  obtain ⟨c,p,q,hc,hp,hq,hbound⟩ := scalar_normalized_log_budget
  refine ⟨c+p*Real.log 13,p/κ,q,by positivity,by positivity,hq,?_⟩
  intro Kcoef Kproj hKcoef hKproj
  have hh := hbound (scalarNormalizationRadius κ Kcoef) Kproj hKproj
  have hr := mul_le_mul_of_nonneg_left (scalar_normalization_radius_log hκ hKcoef) hp
  calc
    _ ≤ c+p*(Real.log 13+(1/κ)*Real.log Kcoef)+q*Real.log Kproj := by linarith
    _ = _ := by ring

 theorem scalar_density_inverse_radius {κ K R : ℝ} (hκ : 0 < κ) (hK : 0 < K)
    (hR : 0 < R) (hbound : 1 ≤ (2:ℝ)^κ*K*R^κ) :
    |R⁻¹| ≤ scalarNormalizationRadius κ K := by
  rw [abs_of_pos (inv_pos.mpr hR)]
  exact (scalar_density_inverse_bound hR hκ hK hbound).trans (Nat.le_ceil _)

end Falconer

end OAI
