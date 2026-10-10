import OAI.MeasureTheory.Falconer.Geometry.MiddleScaleGeometry

namespace OAI

/-! # One fixed angular coarsening works for every interval with the contact margins -/

namespace Falconer

theorem uniform_middle_geometry {σ r γ : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (hγ : 0 < γ) (H C : ℝ) (M₀ : ℕ) :
    ∃ J N₀ : ℕ, ∀ N ≥ N₀, ∀ p v : ℕ, ∀ Δ : ℝ,
      p ≤ v → γ ≤ Δ → Δ*(N:ℝ)-1 ≤ (v-p:ℕ) →
      γ*(N:ℝ) ≤ 2*(p:ℝ)-(v:ℝ) →
      let M := (v-p)-J
      J ≤ v-p ∧ M₀ ≤ M ∧ (N:ℝ)*Δ ≤ 2*(M:ℝ) ∧
      8*(1/4:ℝ)^2/((σ*(2:ℝ)^p)*r) ≤ 1/(2:ℝ)^M ∧
      ((σ*(2:ℝ)^p)*H)*(C/(2:ℝ)^v) ≤ 1/(2:ℝ)^M := by
  obtain ⟨J,hJ⟩ := Regularization.fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) (σ*H*C)
  have hC : σ*H*C ≤ (2:ℝ)^J := by simpa only [Real.rpow_one] using hJ J le_rfl
  obtain ⟨N₁,hN₁⟩ := eventually_uniform_middle_freeze hσ hr hγ
  obtain ⟨N₂,hN₂⟩ := eventually_contact_middle_depth hγ J (M₀+1)
  refine ⟨J,max N₁ N₂,?_⟩
  intro N hN p v Δ hpv hγΔ hgap hmargin
  dsimp only
  obtain ⟨hM,hwidth⟩ := hN₂ N ((le_max_right _ _).trans hN) (v-p) Δ hγΔ hgap
  have hJk : J ≤ v-p := by omega
  refine ⟨hJk,by omega,hwidth,?_,middle_width_rounding p v J hpv hJk hC⟩
  have hh := hN₁ N ((le_max_left _ _).trans hN) p v hpv hmargin
  have hδ : 1/(2:ℝ)^(v-p) ≤ 1/(2:ℝ)^((v-p)-J) :=
    one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
  norm_num only [show 8*(1/4:ℝ)^2 = 1/2 by norm_num]
  exact hh.trans hδ

end Falconer

end OAI
