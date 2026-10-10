import Mathlib
import OAI.Analysis.Commutator.AddField
import OAI.Analysis.Commutator.DiagonalCommute
import OAI.Analysis.Commutator.FieldAdjoint
import OAI.Analysis.Commutator.FieldUniqueness

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace Kadison.Decomposable

variable {Ω H A : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ]
  [CStarAlgebra A]

theorem exists_starHom_fields
    (ρ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (hcomm : ∀ a (s : Set Ω) (hs : MeasurableSet s),
      Commute (ρ a) (indicatorOperator (H:=H) μ s hs)) :
    ∃ (T : A → Ω → H →L[ℂ] H)
      (hm : ∀ a ξ,AEStronglyMeasurable (fun x => T a x ξ) μ)
      (hb : ∀ a,∀ᵐ x ∂μ,‖T a x‖≤‖a‖),
      (∀ a,ρ a=operator μ (T a) (hm a) (hb a)) ∧
      (∀ a b,∀ᵐ x ∂μ,T (a+b) x=T a x+T b x) ∧
      (∀ a b,∀ᵐ x ∂μ,T (a*b) x=T a x*T b x) ∧
      (∀ a,∀ᵐ x ∂μ,T (star a) x=star (T a x)) ∧
      (∀ z : ℂ,∀ᵐ x ∂μ,T (z • (1:A)) x=z • (1:H →L[ℂ] H)) := by
  choose T hm hbn he using fun a => exists_field_of_commutes_indicator μ (ρ a) (hcomm a)
  have hb : ∀ a,∀ᵐ x ∂μ,‖T a x‖≤‖a‖ := fun a =>
    (hbn a).mono (fun _ hx => hx.trans (NonUnitalStarAlgHom.norm_apply_le ρ a))
  have he' (a : A) : ρ a=operator μ (T a) (hm a) (hb a) := by
    apply operator_eq_of_ae_apply
    intro f
    rw [he a]
    exact operator_ae μ (T a) (hm a) (hbn a) f
  refine ⟨T,hm,hb,he',?_,?_,?_,?_⟩
  · intro a b
    apply field_eq_ae_of_operator_eq μ (T (a+b)) (fun x => T a x+T b x)
      (hm (a+b)) (add_measurable μ _ _ (hm a) (hm b)) (hb (a+b))
      (add_field_bound μ _ _ (hb a) (hb b))
    rw [operator_add μ _ _ (hm a) (hm b) (hb a) (hb b),←he',←he',←he',map_add]
  · intro a b
    apply field_eq_ae_of_operator_eq μ (T (a*b)) (fun x => T a x*T b x)
      (hm (a*b)) (mul_measurable μ _ _ (hm a) (hm b)) (hb (a*b))
      (mul_bound μ _ _ (norm_nonneg a) (hb a) (hb b))
    rw [←operator_mul μ _ _ (hm a) (hm b) (norm_nonneg a) (hb a) (hb b),
      ←he',←he',←he',map_mul]
  · intro a
    exact adjoint_ae μ (T a) (T (star a)) (hm a) (hm (star a)) (hb a) (hb (star a))
      (by rw [←he',←he',map_star]; rfl)
  · intro z
    have hc : (z • (1 : Lp H 2 μ →L[ℂ] Lp H 2 μ))=
        operator μ (fun _ => z • (1:H →L[ℂ] H))
          (fun _ => aestronglyMeasurable_const) (Eventually.of_forall (fun _ => le_rfl)) := by
      apply operator_eq_of_ae_apply
      intro f
      exact Lp.coeFn_smul z f
    apply field_eq_ae_of_operator_eq μ (T (z • (1:A))) (fun _ => z • (1:H →L[ℂ] H))
      (hm _) (fun _ => aestronglyMeasurable_const) (hb _)
      (Eventually.of_forall (fun _ => le_rfl))
    rw [←he',←hc,map_smul,map_one]

end Kadison.Decomposable

end

end
end

end OAI
