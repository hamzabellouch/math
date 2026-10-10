import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.FarSourceScaleRegime

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Filter Real
open scoped Topology

theorem far_depth_regime_eventuallyND {σ : ℝ} (hσ : 0<σ) (D : ℝ) :
    ∀ᶠ R : ℝ in atTop, ∀ (N L k : ℕ) (a v : ℝ), R=(2:ℝ)^N →
      a≤k → v-a≤N →
      (k:ℝ)≤v-2*(max L (Nat.ceil (10*σ*N)):ℕ)+D →
      (L:ℝ)≤(v-k)/2+σ*N ∧ 10*σ*N≤v-k ∧ v-k≤2*N := by
  filter_upwards [eventually_ge_atTop ((2:ℝ)^(D/σ))] with R hR
  intro N L k a v hRN hak hv hk
  have hDN : D≤σ*N := by
    rw [hRN,← Real.rpow_natCast (2:ℝ) N] at hR
    have hh := (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ)<2)).mp hR
    exact (div_le_iff₀ hσ).mp hh |>.trans_eq (mul_comm _ _)
  have hL : (L:ℝ)≤(max L (Nat.ceil (10*σ*N)):ℕ) := by exact_mod_cast Nat.le_max_left L _
  have hm : 10*σ*N≤(max L (Nat.ceil (10*σ*N)):ℕ) :=
    (Nat.le_ceil (10*σ*(N:ℝ))).trans (by exact_mod_cast Nat.le_max_right L (Nat.ceil (10*σ*N)))
  have hnonneg : 0≤σ*(N:ℝ) := mul_nonneg hσ.le (Nat.cast_nonneg N)
  have hN : (0:ℝ)≤N := Nat.cast_nonneg N
  exact ⟨by linarith,by linarith,by linarith⟩

theorem far_source_point_regime_eventuallyND {σ : ℝ} (hσ : 0<σ) (hσ₁ : σ≤1) (D : ℝ) :
    ∀ᶠ R : ℝ in atTop, ∀ (N L k : ℕ) (a v dist : ℝ), R=(2:ℝ)^N →
      a≤k → v-a≤N →
      (k:ℝ)≤v-2*(max L (Nat.ceil (10*σ*N)):ℕ)+D →
      (2:ℝ)^(-(k:ℝ))/4≤dist →
      1≤ shellEffectiveScaleND L R σ ∧ shellEffectiveScaleND L R σ≤R^2 ∧
      R^σ≤(2:ℝ)^v*dist ∧ (shellEffectiveScaleND L R σ)^2/((2:ℝ)^v*dist)≤R^(-σ) := by
  filter_upwards [far_depth_regime_eventuallyND hσ D,
    far_source_scale_regime_eventuallyND hσ hσ₁ (by norm_num : (0:ℝ)<1/4)] with R hdepth hscale
  intro N L k a v dist hRN hak hv hk hdist
  obtain ⟨hl,hqlo,hqup⟩ := hdepth N L k a v hRN hak hv hk
  obtain ⟨hl',hqlo',hqup'⟩ := far_source_exponentsND hl hqlo hqup
  rw [← hRN] at hl' hqlo' hqup'
  have hΛ : (1/4:ℝ)*(2:ℝ)^(v-k)≤(2:ℝ)^v*dist := by
    calc
      _ = (2:ℝ)^v*((2:ℝ)^(-(k:ℝ))/4) := by
        rw [Real.rpow_sub (by norm_num : (0:ℝ)<2),Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdist (by positivity)
  obtain ⟨h₁,h₂,h₃,h₄,_⟩ := hscale L (v-k) ((2:ℝ)^v*dist) hl' hqlo' hqup' hΛ
  exact ⟨h₁,h₂,h₃,h₄⟩

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
