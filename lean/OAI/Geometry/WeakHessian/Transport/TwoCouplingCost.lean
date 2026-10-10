import Mathlib
import OAI.Geometry.WeakHessian.Transport.PlanEnergy

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

omit [ProperSpace X] in
lemma two_coupling_cost_lower {μ₀ μ₁ ν : Measure X} {q₀ q₁ : Measure (X×X)}
    [IsProbabilityMeasure q₀] [IsProbabilityMeasure q₁]
    (h₀ : IsCoupling q₀ μ₀ ν) (h₁ : IsCoupling q₁ μ₁ ν)
    (ht₀ : QuadraticTransportCost q₀ ≠ ∞) (ht₁ : QuadraticTransportCost q₁ ≠ ∞)
    (x₀ x₁ : X) {r₀ r₁ : ℝ}
    (hs₀ : ∀ᵐ x ∂μ₀,dist x x₀ ≤ r₀) (hs₁ : ∀ᵐ x ∂μ₁,dist x x₁ ≤ r₁) :
    (max 0 (dist x₀ x₁-r₀-r₁))^2/2 ≤
      (QuadraticTransportCost q₀).toReal+(QuadraticTransportCost q₁).toReal := by
  let : Nonempty X := ⟨x₀⟩
  obtain ⟨p,hp,hp₀,hp₁,hjoin⟩ := exists_fiber_gluing_supported q₀ q₁ Prod.snd Prod.snd
    measurable_snd measurable_snd (h₀.2.trans h₁.2.symm)
  let := hp
  have H₀ : ∀ᵐ z : X×X ∂q₀,dist z.1 x₀ ≤ r₀ :=
    ae_of_ae_map measurable_fst.aemeasurable (by rwa [h₀.1])
  have H₁ : ∀ᵐ z : X×X ∂q₁,dist z.1 x₁ ≤ r₁ :=
    ae_of_ae_map measurable_fst.aemeasurable (by rwa [h₁.1])
  have Hp₀ : ∀ᵐ z : (X×X)×(X×X) ∂p,dist z.1.1 x₀ ≤ r₀ :=
    ae_of_ae_map measurable_fst.aemeasurable (by rwa [hp₀])
  have Hp₁ : ∀ᵐ z : (X×X)×(X×X) ∂p,dist z.2.1 x₁ ≤ r₁ :=
    ae_of_ae_map measurable_snd.aemeasurable (by rwa [hp₁])
  have hi₀ := (show MeasurePreserving Prod.fst p q₀ from ⟨measurable_fst,hp₀⟩).integrable_comp_of_integrable
    (integrable_squared_distance_of_cost ht₀)
  have hi₁ := (show MeasurePreserving Prod.snd p q₁ from ⟨measurable_snd,hp₁⟩).integrable_comp_of_integrable
    (integrable_squared_distance_of_cost ht₁)
  have H : ∀ᵐ z : (X×X)×(X×X) ∂p,(max 0 (dist x₀ x₁-r₀-r₁))^2/2 ≤
      dist z.1.1 z.1.2^2+dist z.2.1 z.2.2^2 := by
    filter_upwards [Hp₀,Hp₁,hjoin] with z hz₀ hz₁ hj
    have hd : dist x₀ x₁-r₀-r₁ ≤ dist z.1.1 z.1.2+dist z.2.1 z.2.2 := by
      have H := dist_triangle x₀ z.1.1 x₁
      have H' := dist_triangle z.1.1 z.1.2 x₁
      have H'' := dist_triangle z.2.2 z.2.1 x₁
      rw [dist_comm x₀ z.1.1] at H
      rw [dist_comm z.2.2 z.2.1] at H''
      rw [hj]
      rw [hj] at H'
      linarith
    have hh : max 0 (dist x₀ x₁-r₀-r₁) ≤ dist z.1.1 z.1.2+dist z.2.1 z.2.2 :=
      max_le (add_nonneg dist_nonneg dist_nonneg) hd
    have hn := le_max_left 0 (dist x₀ x₁-r₀-r₁)
    nlinarith [sq_nonneg (dist z.1.1 z.1.2-dist z.2.1 z.2.2)]
  have HH := integral_mono_ae (integrable_const ((max 0 (dist x₀ x₁-r₀-r₁))^2/2))
    (hi₀.add hi₁) H
  dsimp only [Function.comp_def] at hi₀ hi₁
  simp only [Function.comp_def,Pi.add_apply,integral_const,probReal_univ,one_smul] at HH
  rw [integral_add hi₀ hi₁] at HH
  have he₀ : (∫ z : (X×X)×(X×X),dist z.1.1 z.1.2^2 ∂p) =
      (QuadraticTransportCost q₀).toReal := by
    rw [quadraticTransportCost_eq_integral ht₀,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
    rw [← hp₀]
    exact (integral_map measurable_fst.aemeasurable
      (show AEStronglyMeasurable (fun x : X×X => dist x.1 x.2^2) (p.map Prod.fst) from
        ((continuous_fst.dist continuous_snd).pow 2).aestronglyMeasurable)).symm
  have he₁ : (∫ z : (X×X)×(X×X),dist z.2.1 z.2.2^2 ∂p) =
      (QuadraticTransportCost q₁).toReal := by
    rw [quadraticTransportCost_eq_integral ht₁,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
    rw [← hp₁]
    exact (integral_map measurable_snd.aemeasurable
      (show AEStronglyMeasurable (fun x : X×X => dist x.1 x.2^2) (p.map Prod.snd) from
        ((continuous_fst.dist continuous_snd).pow 2).aestronglyMeasurable)).symm
  simpa only [Function.comp_def,Pi.add_apply,he₀,he₁] using HH

end WeakHessian

end
end

end OAI
