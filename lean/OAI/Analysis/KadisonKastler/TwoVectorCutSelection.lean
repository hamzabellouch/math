import OAI.Analysis.KadisonKastler.CentralDefectSelfAdjoint
import OAI.Analysis.KadisonKastler.GoodProjectionCut

namespace OAI

/-! # Choosing a projection from two relative mean bounds -/

namespace KadisonKastler

open MeasureTheory Generator Generator.Tracial

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem exists_two_relative_bounds (f g h : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    (hf₀ : ∀ x, 0 ≤ f x) (hh₀ : ∀ x, 0 ≤ h x)
    {α K : ℝ} (hα : 0 < α) (hK : 0 < K)
    (hmean : α*(∫ x, f x ∂μ)+K*(∫ x, h x ∂μ) < α*K*(∫ x, g x ∂μ)) :
    ∃ x, f x < K*g x ∧ h x < α*g x := by
  have hint : 0 < ∫ x, α*K*g x-(α*f x+K*h x) ∂μ := by
    have he := integral_sub (hg.const_mul (α*K)) ((hf.const_mul α).add (hh.const_mul K))
    simp only [Pi.add_apply] at he
    rw [he,integral_add (hf.const_mul _) (hh.const_mul _),
      integral_const_mul,integral_const_mul,integral_const_mul]
    linarith
  obtain ⟨x,hx⟩ : ∃ x, 0 < α*K*g x-(α*f x+K*h x) := by
    by_contra hn
    push Not at hn
    exact (not_le_of_gt hint) (integral_nonpos hn)
  refine ⟨x,?_,?_⟩
  · have hn := mul_nonneg hK.le (hh₀ x)
    nlinarith
  · have hn := mul_nonneg hα.le (hf₀ x)
    nlinarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_projection_two_relative_bounds
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) (P : X → AlgebraProjection M)
    (hmass : Integrable (fun t => ‖(P t).val.val ξ‖^2+‖(P t).val.val η‖^2) μ)
    (hξ : Integrable (fun t => ‖centralVectorDefect J ξ (P t).val.val‖^2) μ)
    (hη : Integrable (fun t => ‖centralVectorDefect J η (P t).val.val‖^2) μ)
    {α K : ℝ} (hα : 0 < α) (hK : 0 < K)
    (hmean : α*(∫ t, ‖(P t).val.val ξ‖^2+‖(P t).val.val η‖^2 ∂μ)+
      K*(∫ t, ‖centralVectorDefect J ξ (P t).val.val‖^2 ∂μ) <
        α*K*(∫ t, ‖centralVectorDefect J η (P t).val.val‖^2 ∂μ)) :
    ∃ p : AlgebraProjection M,
      ‖p.val.val ξ‖^2+‖p.val.val η‖^2 < K*‖centralVectorDefect J η p.val.val‖^2 ∧
      ‖centralVectorDefect J ξ p.val.val‖^2 < α*‖centralVectorDefect J η p.val.val‖^2 := by
  obtain ⟨t,ht⟩ := exists_two_relative_bounds _ _ _ hmass hη hξ
    (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) (fun _ => sq_nonneg _)
    hα hK hmean
  exact ⟨P t,ht⟩

end

end KadisonKastler

end OAI
