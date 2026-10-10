import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatRegularity
import OAI.Geometry.WeakHessian.HeatFlow.MixedGeneratorPairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile190
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

def BoundedLipschitzRepresentative (m : Measure X) (u : X → ℝ) : Prop :=
  ∃ v : X → ℝ,GloballyLipschitz v ∧ BoundedFunction v ∧ v =ᵐ[m] u

omit [SigmaFinite m] in
lemma IsLaplacian.mixed_pairing_ae (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u v A C ξ B : X → ℝ} (hu : IsLaplacian m u A) (hv : IsLaplacian m v C)
    (hξ : IsLaplacian m ξ B) (huR : BoundedLipschitzRepresentative m u)
    (hvR : BoundedLipschitzRepresentative m v)
    {Cξ : ℝ} (hξB : ∀ᵐ x ∂m,|ξ x| ≤ Cξ) :
    2*(∫ x,ξ x*gamma m u v x ∂m) =
      (∫ x,u x*v x*B x ∂m)-(∫ x,A x*v x*ξ x ∂m)-(∫ x,u x*C x*ξ x ∂m) := by
  obtain ⟨u0,⟨L,hL⟩,⟨Cu,hCu⟩,hue⟩ := huR
  obtain ⟨v0,⟨M,hM⟩,⟨Cv,hCv⟩,hve⟩ := hvR
  have H := (hu.congr_ae hue.symm .rfl).mixed_pairing hfin hpar
    (hv.congr_ae hve.symm .rfl) hξ hL hM hCu hCv hξB
  have e1 : (∫ x,ξ x*gamma m u0 v0 x ∂m) = ∫ x,ξ x*gamma m u v x ∂m :=
    integral_congr_ae (.fun_mul .rfl (gamma_congr_ae hue hve))
  have e2 : (∫ x,u0 x*v0 x*B x ∂m) = ∫ x,u x*v x*B x ∂m :=
    integral_congr_ae ((hue.fun_mul hve).fun_mul .rfl)
  have e3 : (∫ x,A x*v0 x*ξ x ∂m) = ∫ x,A x*v x*ξ x ∂m :=
    integral_congr_ae ((EventuallyEq.fun_mul .rfl hve).fun_mul .rfl)
  have e4 : (∫ x,u0 x*C x*ξ x ∂m) = ∫ x,u x*C x*ξ x ∂m :=
    integral_congr_ae ((hue.fun_mul .rfl).fun_mul .rfl)
  rwa [e1,e2,e3,e4] at H

omit [SigmaFinite m] in
lemma IsLaplacian.square_gamma_pairing_ae (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A ξ B : X → ℝ}
    (hu : IsLaplacian m u A) (hξ : IsLaplacian m ξ B)
    (huR : BoundedLipschitzRepresentative m u) {Cξ : ℝ}
    (hξB : ∀ᵐ x ∂m,|ξ x| ≤ Cξ) :
    (∫ x,ξ x*gamma m u u x ∂m) =
      (1/2)*(∫ x,(u x)^2*B x ∂m)-(∫ x,u x*A x*ξ x ∂m) := by
  have H := hu.mixed_pairing_ae hfin hpar hu hξ huR huR hξB
  have e1 : (∫ x,u x*u x*B x ∂m) = ∫ x,(u x)^2*B x ∂m := by simp only [pow_two]
  have e2 : (∫ x,A x*u x*ξ x ∂m) = ∫ x,u x*A x*ξ x ∂m := by congr 1; funext x; ring
  rw [e1,e2] at H
  linarith

lemma RCD.weighted_heat_boundedLipschitzRepresentative {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    {u A : Lp ℝ 2 (exponentialMeasure m V)}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {Bu BA : ℝ} (hBu : 0 ≤ Bu) (hBA : 0 ≤ BA)
    (hub : ∀ᵐ x ∂exponentialMeasure m V,|u x| ≤ Bu)
    (hAb : ∀ᵐ x ∂exponentialMeasure m V,|A x| ≤ BA) {t : ℝ} (ht : 0 ≤ t) :
    BoundedLipschitzRepresentative (exponentialMeasure m V) (cheegerHeat h t u) := by
  obtain ⟨M,hM⟩ := hrcd.weighted_heat_uniform_lipschitz hN hfull hfin o hV hBV h hu hBu hBA hub hAb
  obtain ⟨g,hg,hge⟩ := hM t ht
  refine ⟨g,⟨M,hg⟩,⟨Bu,?_⟩,hge⟩
  apply continuous_le_of_ae_le hfull hg.continuous.abs continuous_const
  apply (Measure.absolutelyContinuous_of_le_smul (exponentialMeasure_comparable (m := m) hBV).1).ae_le
  filter_upwards [hge,cheegerHeat_bounded h ht hBu u hub] with x hx hb
  rwa [hx]
end WeakHessian

end
end InlinedFile190

end OAI
