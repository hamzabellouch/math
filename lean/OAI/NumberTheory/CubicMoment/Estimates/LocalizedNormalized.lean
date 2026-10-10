import OAI.NumberTheory.CubicMoment.Estimates.LogLocalizedIntegral
import OAI.NumberTheory.CubicMoment.Estimates.LocalizedPowerScale
import OAI.NumberTheory.CubicMoment.Estimates.HeightBilinearValue

namespace OAI

/-! At a fixed positive power cell width, the actual integrated bilinear
form has the Patterson-scale power saving uniformly in the cutoff center. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace CubicFirstMoment

theorem localized_integral_power_saving
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (γ K Z₀ : ℝ), 0 < γ ∧ 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ T M : ℝ),
      Z₀ ≤ Z → 2*Z^(3/2:ℝ) ≤ A → A ≤ Z^(2+γ) → 0 < X₀ → Z^(1/50:ℝ) ≤ T → 0 ≤ M →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
      Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
      (∀ t, ‖h t‖ ≤ M) → (∀ t, t ∉ dyadicHeightSupport T → h t = 0) →
      (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ M) →
      (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
      ‖heightBilinearValue P S α β h X₀ T‖ ≤
        K*M*Real.sqrt (A^(2/3:ℝ)*Z^(2/3-2*γ/3))*
          Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2) := by
  obtain ⟨d,K,hK,hbound⟩ := localized_height_integral_bound hMV hC hHuxley
  let γ := thinCellExponent d
  have hγ : 0 < γ := thinCellExponent_pos d
  obtain ⟨Z₁,hZ₁⟩ := eventually_atTop.mp ((tendsto_rpow_atTop hγ).eventually_ge_atTop 8)
  refine ⟨γ,4*K,max 65536 Z₁,hγ,by positivity,?_⟩
  intro P S α β Z A X₀ T M hZ hA hAu hX hT hM hP hS h hi hd hi' hd' hi'' hh hs hh2 hs2
  have hZbig : 65536 ≤ Z := (le_max_left _ _).trans hZ
  have hZ1 : 1 ≤ Z := by linarith
  have hZp : 0 < Z := by linarith
  have hAp : 0 < A := lt_of_lt_of_le (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  have hJ8 : 8 ≤ Z^γ := hZ₁ Z ((le_max_right _ _).trans hZ)
  have hJ1 : 1 ≤ Z^γ := by linarith
  have hb := hbound (Z^γ) hJ8 P S α β Z A X₀ T M hZbig hA hX hT hM hP hS
    h hi hd hi' hd' hi'' hh hs hh2 hs2
  have hf := localized_height_ratio hJ1 (localized_height_power d hZ1 hT)
  have hr := localized_root_scale d hZ1 hAp hAu
  have hc : K*(1+Z^γ*(Z^γ/T)^2)*M*
      (Real.sqrt (A/Z^γ)+Real.sqrt ((Z^γ)^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ))) ≤
      (4*K)*M*Real.sqrt (A^(2/3:ℝ)*Z^(2/3-2*γ/3)) := by
    calc
      _ ≤ K*2*M*(2*Real.sqrt (A^(2/3:ℝ)*Z^(2/3-2*γ/3))) := by
        gcongr
        · linarith
      _ = _ := by ring
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

end CubicFirstMoment

end

end OAI
