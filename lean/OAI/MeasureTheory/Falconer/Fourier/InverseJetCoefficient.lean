import OAI.MeasureTheory.Falconer.Fourier.InverseClassIntegration
import OAI.MeasureTheory.Falconer.Shells.NormalizedShellCoefficients

namespace OAI

/-! # The radial inverse power pays only the newly added jets -/

namespace Falconer
open MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorInverseSymbols
variable {m K L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
  {f : DescriptorJetSymbol (m+1) K L F D}
  {g : DescriptorJetSymbol (m+1) K L G D} {j R : ℕ} {A B : ℝ}

theorem normalized_coefficient_le (T : DescriptorInverseSymbols f g j R A B)
    (hD : 0 < D) (N : ℕ) (σ Af Ag U : ℝ) {E Λ V h : ℝ}
    (hE : 1 ≤ E) (hDE : D ≤ E)
    (hF : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hG : ∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hΛ : 0 < Λ) (hV : 0 < V) (hh : 0 ≤ h)
    (hEΛ : E^2 ≤ Λ) (hΛV : Λ ≤ 4*V) (a : DescriptorInverseIndex f g j) :
    ‖((Λ^h*(Λ^j)⁻¹/(V^h) : ℝ) : ℂ)*
      (T.coefficient N σ Af Ag U U a : ℂ)‖ ≤
      (|U*A| *|U*B| *|Af⁻¹| *|Ag⁻¹|)*4^h := by
  have hγ : 0 ≤ Λ^h*(Λ^j)⁻¹/(V^h) := by positivity
  have hc := T.coefficient_abs_le hD N σ Af Ag U U hE hDE hF hG a
  have hr := normalized_stationary_coefficient_le
    (p := 2*j) (q := 0) (j := j) (by omega) hΛ hE hV hh hEΛ hΛV
  simp only [add_zero] at hr
  have hr' : Λ^h*(Λ^j)⁻¹*E^(2*j)/(V^h) ≤ (4:ℝ)^h :=
    (le_abs_self _).trans hr
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg hγ]
  calc
    _ ≤ (Λ^h*(Λ^j)⁻¹/(V^h))*(E^(2*j)*|U*A| *|U*B| *|Af⁻¹| *|Ag⁻¹|) :=
      mul_le_mul_of_nonneg_left hc hγ
    _ = (|U*A| *|U*B| *|Af⁻¹| *|Ag⁻¹|)*(Λ^h*(Λ^j)⁻¹*E^(2*j)/(V^h)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr' (by positivity)

end DescriptorInverseSymbols
end Falconer

end OAI
