import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Shells.ShellEffectiveScale

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Filter Real
open scoped Topology

lemma far_source_scale_regimeND {R σ q c Λ : ℝ} (l : ℕ)
    (hR : 1 ≤ R) (hσ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (hc : 0<c)
    (hl : (2:ℝ)^l ≤ (2:ℝ)^(q/2)*R^σ)
    (hqlo : R^(10*σ) ≤ (2:ℝ)^q) (hqup : (2:ℝ)^q ≤ R^2)
    (hΛ : c*(2:ℝ)^q ≤ Λ) :
    1 ≤ shellEffectiveScaleND l R σ ∧ shellEffectiveScaleND l R σ ≤ R^2 ∧
    c*R^(10*σ) ≤ Λ ∧ (shellEffectiveScaleND l R σ)^2/Λ ≤ c⁻¹*R^(-8*σ) ∧
    (2:ℝ)^(-q)*(sourceMaskScaleND l R σ)^2 ≤ 1 := by
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hQp : 0<(2:ℝ)^q := Real.rpow_pos_of_pos (by norm_num) _
  have hΛp : 0<Λ := (mul_pos hc hQp).trans_le hΛ
  have hRs : 1≤R^σ := Real.one_le_rpow hR hσ
  have hu := shell_effective_scale_upperND l hRp hl
  have hsquare := shell_effective_scale_sqND l hRp hl
  have hhalf : (2:ℝ)^(q/2) ≤ R := by
    nlinarith [dyadic_half_sqND q, Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (q/2)]
  have hle (u : ℝ) (hu : u ≤ 0) : R^u ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hR hu
  have hnorm : (shellEffectiveScaleND l R σ)^2 ≤ (2:ℝ)^q*R^(-8*σ) := by
    apply hsquare.trans
    apply max_le
    · calc
        R^(2*σ) = R^(10*σ)*R^(-8*σ) := by rw [← Real.rpow_add hRp]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hqlo (Real.rpow_nonneg hRp.le _)
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) hQp.le
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact one_le_mul_of_one_le_of_one_le hRs (sourceMaskScaleND_one_le l R σ)
  · apply hu.trans
    apply max_le
    · simpa using Real.rpow_le_rpow_of_exponent_le hR (show σ ≤ (2:ℝ) by linarith)
    · calc
        _ ≤ (2:ℝ)^(q/2) := mul_le_of_le_one_right (by positivity) (hle (-48*σ) (by linarith))
        _ ≤ R := hhalf
        _ ≤ R^2 := by nlinarith
  · exact (mul_le_mul_of_nonneg_left hqlo hc.le).trans hΛ
  · calc
      _ ≤ ((2:ℝ)^q*R^(-8*σ))/(c*(2:ℝ)^q) :=
        div_le_div₀ (by positivity) hnorm (mul_pos hc hQp) hΛ
      _ = _ := by field_simp
  · have hQle : sourceMaskScaleND l R σ ≤ shellEffectiveScaleND l R σ := by
      exact le_mul_of_one_le_left (sourceMaskScaleND_pos l R σ).le hRs
    have hsq : (sourceMaskScaleND l R σ)^2 ≤ (2:ℝ)^q :=
      (pow_le_pow_left₀ (sourceMaskScaleND_pos l R σ).le hQle 2).trans
        (hnorm.trans (mul_le_of_le_one_right hQp.le (hle (-8*σ) (by linarith))))
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    exact (inv_mul_le_one₀ hQp).mpr hsq

theorem far_source_scale_regime_eventuallyND {σ c : ℝ} (hσ : 0<σ) (hσ₁ : σ≤1) (hc : 0<c) :
    ∀ᶠ R : ℝ in atTop, ∀ (l : ℕ) (q Λ : ℝ),
      (2:ℝ)^l ≤ (2:ℝ)^(q/2)*R^σ → R^(10*σ) ≤ (2:ℝ)^q → (2:ℝ)^q ≤ R^2 →
      c*(2:ℝ)^q ≤ Λ →
      1 ≤ shellEffectiveScaleND l R σ ∧ shellEffectiveScaleND l R σ ≤ R^2 ∧
      R^σ ≤ Λ ∧ (shellEffectiveScaleND l R σ)^2/Λ ≤ R^(-σ) ∧
      (2:ℝ)^(-q)*(sourceMaskScaleND l R σ)^2 ≤ 1 := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (by linarith : (0:ℝ)<7*σ)).eventually_ge_atTop c⁻¹] with R hR hlarge
  intro l q Λ hl hqlo hqup hΛ
  have hRp : 0<R := zero_lt_one.trans_le hR
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := far_source_scale_regimeND l hR hσ.le hσ₁ hc hl hqlo hqup hΛ
  refine ⟨h₁,h₂,?_,?_,h₅⟩
  · have hcR : 1 ≤ c*R^(7*σ) := by simpa only [mul_comm] using (inv_le_iff_one_le_mul₀ hc).mp hlarge
    have hRs : R^σ ≤ R^(3*σ) := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
    apply le_trans _ h₃
    calc
      _ ≤ R^(3*σ) := hRs
      _ ≤ (c*R^(7*σ))*R^(3*σ) := le_mul_of_one_le_left (Real.rpow_nonneg hRp.le _) hcR
      _ = _ := by rw [mul_assoc,← Real.rpow_add hRp]; congr 2; ring
  · apply h₄.trans
    calc
      _ ≤ R^(7*σ)*R^(-8*σ) := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hRp.le _)
      _ = _ := by rw [← Real.rpow_add hRp]; congr 1; ring

lemma far_source_exponentsND {N l : ℕ} {σ q : ℝ}
    (hl : (l:ℝ) ≤ q/2+σ*N) (hqlo : 10*σ*N ≤ q) (hqup : q ≤ 2*N) :
    (2:ℝ)^l ≤ (2:ℝ)^(q/2)*((2:ℝ)^N)^σ ∧
    ((2:ℝ)^N)^(10*σ) ≤ (2:ℝ)^q ∧ (2:ℝ)^q ≤ ((2:ℝ)^N)^2 := by
  have h₁ : ((2:ℝ)^N)^σ=(2:ℝ)^((N:ℝ)*σ) := by
    rw [← Real.rpow_natCast (2:ℝ) N,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  have h₂ : ((2:ℝ)^N)^(10*σ)=(2:ℝ)^((N:ℝ)*(10*σ)) := by
    rw [← Real.rpow_natCast (2:ℝ) N,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  have h₃ : ((2:ℝ)^N)^2=(2:ℝ)^((N:ℝ)*2) := by
    rw [← Real.rpow_natCast (2:ℝ) N,← Real.rpow_natCast ((2:ℝ)^(N:ℝ)) 2,
      ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    norm_num
  rw [h₁,h₂,h₃,← Real.rpow_add (by norm_num : (0:ℝ)<2),← Real.rpow_natCast (2:ℝ) l]
  exact ⟨Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith),
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith),
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)⟩

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
