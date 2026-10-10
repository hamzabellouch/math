import OAI.Geometry.RCD.Heat.KernelHeatL2Representation

namespace OAI

/-! # Bounded positive and negative parts of the original L2 datum -/

open Filter MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem bounded_lp_parts (f : Lp ℝ 2 μ) (A : ℝ≥0) (hf : ∀ᵐ x ∂μ, |f x| ≤ A) :
    0 ≤ Lp.posPart f ∧ 0 ≤ Lp.negPart f ∧
      (∀ᵐ x ∂μ, |Lp.posPart f x| ≤ A) ∧
      (∀ᵐ x ∂μ, |Lp.negPart f x| ≤ A) ∧ f=Lp.posPart f-Lp.negPart f := by
  have hp := Lp.coeFn_posPart f
  have hn := Lp.coeFn_negPart_eq_max f
  refine ⟨(Lp.coeFn_nonneg _).mp ?_,(Lp.coeFn_nonneg _).mp ?_,?_,?_,?_⟩
  · exact hp.mono fun x hx => hx ▸ le_max_right _ _
  · exact hn.mono fun x hx => hx ▸ le_max_right _ _
  · filter_upwards [hp,hf] with x hx hb
    rw [hx,abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans hb) A.coe_nonneg
  · filter_upwards [hn,hf] with x hx hb
    rw [hx,abs_of_nonneg (le_max_right _ _)]
    exact max_le ((neg_le_abs _).trans hb) A.coe_nonneg
  · apply Lp.ext
    filter_upwards [hp,hn,Lp.coeFn_sub (Lp.posPart f) (Lp.negPart f)] with x hp hn he
    dsimp only [Pi.sub_apply] at he
    rw [he,hp,hn]
    by_cases hx : 0 ≤ f x
    · rw [max_eq_left hx,max_eq_right (neg_nonpos.mpr hx),sub_zero]
    · rw [max_eq_right (le_of_not_ge hx),max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))]
      ring

end RegularPointCoordinates

end

end OAI
