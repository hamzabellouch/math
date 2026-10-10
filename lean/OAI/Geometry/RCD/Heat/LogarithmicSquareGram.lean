import OAI.Geometry.RCD.Heat.HessianLogarithmicDirections

namespace OAI

/-! # Actual Sobolev representatives for squared logarithmic gradients -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem exists_local_log_square_gram {Ω : Set X}
    (u U G : SobolevSpace μ Q) (M : ℝ≥0)
    (hG : SobolevSpace.toLp μ Q G =ᵐ[μ.restrict Ω] localGamma μ Q u u)
    (hGB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q G x| ≤ M)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hu : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.toLp μ Q u x ∈ Icc a b)
    (hU : SobolevSpace.toLp μ Q U =ᵐ[μ.restrict Ω]
      fun x => Real.log (SobolevSpace.toLp μ Q u x)) :
    ∃ H : SobolevSpace μ Q,
      (SobolevSpace.toLp μ Q H =ᵐ[μ.restrict Ω] localGamma μ Q U U) ∧
      ∃ B : ℝ≥0, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q H x| ≤ B := by
  obtain ⟨φ,ψ,χ,C,D,B,E,hφ,hψ,-,hφ0,hψ0,hdφ,-,hB,-,he⟩ :=
    exists_local_smooth_log ha hab
  let V := SobolevSpace.comp μ Q hφ hφ0 u
  let P := SobolevSpace.comp μ Q hψ hψ0 u
  have hP : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q P x| ≤ B := by
    filter_upwards [SobolevSpace.comp_coe μ Q hψ hψ0 u] with x hx
    exact hx ▸ hB _
  let R := SobolevSpace.product μ Q P G B M
  have hR := SobolevSpace.product_coe μ Q P G B M hP hGB
  have hRB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q R x| ≤ B*M := by
    filter_upwards [hR,hP,hGB] with x hx hp hg
    rw [hx,abs_mul]
    exact mul_le_mul hp hg (abs_nonneg _) B.coe_nonneg
  let H := SobolevSpace.product μ Q P R B (B*M)
  have hH := SobolevSpace.product_coe μ Q P R B (B*M) hP hRB
  have hV : SobolevSpace.toLp μ Q V =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q U := by
    filter_upwards [ae_restrict_of_ae (SobolevSpace.comp_coe μ Q hφ hφ0 u),hu,hU]
      with x hx hux hUx
    exact (hx.trans (he _ hux).1).trans hUx.symm
  refine ⟨H,?_,B*(B*M),?_⟩
  · filter_upwards [ae_restrict_of_ae hH,ae_restrict_of_ae hR,hG,
      ae_restrict_of_ae (SobolevSpace.comp_coe μ Q hψ hψ0 u),
      ae_restrict_of_ae (localGamma_comp_C1 μ Q u V hφ hφ0 hψ.continuous hdφ B hB),
      ae_restrict_of_ae (localGamma_comp_C1_right μ Q u u hφ hφ0 hψ.continuous hdφ B hB),
      localGamma_pair_congr_ae μ Q hV hV] with x hHx hRx hGx hPx hleft hright hsame
    rw [hHx,hRx,hGx,hPx,← hsame,hleft,hright]
    rfl
  · filter_upwards [hH,hP,hRB] with x hx hp hr
    rw [hx,abs_mul]
    exact mul_le_mul hp hr (abs_nonneg _) B.coe_nonneg

end RegularPointCoordinates

end

end OAI
