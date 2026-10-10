import OAI.MeasureTheory.Falconer.Estimates.RotatedInverseExpansion
import OAI.MeasureTheory.Falconer.Shells.NormalizedShellCoefficients
import OAI.MeasureTheory.Falconer.Fourier.MaskJetCount

namespace OAI

/-! # Exact added-order radius cost in the rotated root inverse -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem rootInverseTerm_order (m j : ℕ) (F : Finset PolicyDescriptor)
    (a : RootInverseIndex m j F) :
    (∑ b, ((rootInverseTerm m j F a).jet b).order) ≤ 2*j := by
  simpa only [MaskJetTerm.order,Nat.zero_add,rootInverseTerm] using
    (MaskJetExpansion.product_hasOrder (ι := {b // b ∈ F} ⊕ {b // b ∈ F})).inverse (m := m) j a

theorem card_rootInverseIndex (m j : ℕ) (F : Finset PolicyDescriptor) :
    Fintype.card (RootInverseIndex m j F) =
      MaskJetExpansion.inverseMultiplicity (m+2) j*(1+2*F.card*(m+3))^(2*j) := by
  rw [MaskJetExpansion.card_inverse_product,Fintype.card_sum]
  simp only [Fintype.card_coe]
  congr 3
  ring

theorem rootInverseWeight_nonneg (m j : ℕ) (F : Finset PolicyDescriptor) (N : ℕ) (σ : ℝ)
    (a : RootInverseIndex m j F) : 0 ≤ rootInverseWeight m j F N σ a := by
  apply Finset.prod_nonneg
  intro b _
  apply pow_nonneg
  apply inv_nonneg.mpr
  cases b with
  | inl b => exact (descriptorMaskRadius_pos N σ b).le
  | inr b => exact (descriptorMaskRadius_pos N σ b).le

theorem rootInverseWeight_le (m j : ℕ) (F : Finset PolicyDescriptor) (N : ℕ) (σ : ℝ)
    {E : ℝ} (hE : 1 ≤ E)
    (hF : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (a : RootInverseIndex m j F) : rootInverseWeight m j F N σ a ≤ E^(2*j) := by
  have hr (b) : 0 ≤ (rootInverseRadii F N σ b)⁻¹ := by
    cases b with
    | inl b => exact inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le
    | inr b => exact inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le
  have hbound (b) : (rootInverseRadii F N σ b)⁻¹ ≤ E := by
    cases b with
    | inl b => exact hF b b.property
    | inr b => exact hF b b.property
  calc
    _ ≤ ∏ b : {b // b ∈ F} ⊕ {b // b ∈ F}, E^((rootInverseTerm m j F a).jet b).order :=
      Finset.prod_le_prod₀ (fun b _ => pow_nonneg (hr b) _)
        (fun b _ => pow_le_pow_left₀ (hr b) (hbound b) _)
    _ = E^(∑ b, ((rootInverseTerm m j F a).jet b).order) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ E^(2*j) := pow_le_pow_right₀ hE (rootInverseTerm_order m j F a)

theorem rotated_root_normalized_coefficient_le (m j : ℕ) (F : Finset PolicyDescriptor)
    (N : ℕ) (σ U A : ℝ) {E Λ V h : ℝ} (hE : 1 ≤ E)
    (hF : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hΛ : 0 < Λ) (hV : 0 < V) (hh : 0 ≤ h)
    (hEΛ : E^2 ≤ Λ) (hΛV : Λ ≤ 4*V) (a : RootInverseIndex m j F) :
    ‖((Λ^h*(Λ^j)⁻¹/(V^h) : ℝ) : ℂ)*
      (rootInverseWeight m j F N σ a*(U*A)*U : ℝ)‖ ≤ (|U*A| * |U|)*4^h := by
  have hγ : 0 ≤ Λ^h*(Λ^j)⁻¹/(V^h) := by positivity
  have hr := normalized_stationary_coefficient_le
    (p := 2*j) (q := 0) (j := j) (by omega) hΛ hE hV hh hEΛ hΛV
  simp only [add_zero] at hr
  have hr' : Λ^h*(Λ^j)⁻¹*E^(2*j)/(V^h) ≤ (4:ℝ)^h := (le_abs_self _).trans hr
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg hγ,abs_mul,abs_mul,abs_of_nonneg (rootInverseWeight_nonneg m j F N σ a)]
  calc
    _ ≤ (Λ^h*(Λ^j)⁻¹/(V^h))*(E^(2*j)*|U*A| * |U|) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (rootInverseWeight_le m j F N σ hE hF a) (abs_nonneg _))
          (abs_nonneg _)) hγ
    _ = (|U*A| * |U|)*(Λ^h*(Λ^j)⁻¹*E^(2*j)/(V^h)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr' (by positivity)

end Falconer

end OAI
