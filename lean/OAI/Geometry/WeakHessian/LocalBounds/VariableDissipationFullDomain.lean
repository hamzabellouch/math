import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.BoundedGraphCore
import OAI.Geometry.WeakHessian.HeatFlow.VariableDissipationGenerator

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_variable_full_generator {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T : ℝ} (hT : 0 ≤ T) :
    HeatVariableDissipation h (fun x => K-a*G x) f ξ T := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  obtain ⟨vs,As,hg,hvb,hAb,hvs,hAslim⟩ := cheeger_bounded_graph_core h hf
  have hfS : Sobolev ν (f : X → ℝ) := (identified_sobolev_iff_energy hnfin hID).mpr hf.1
  have hvS (n : ℕ) : Sobolev ν (vs n : X → ℝ) := (identified_sobolev_iff_energy hnfin hID).mpr (hg n).1
  obtain ⟨hE,M,hM⟩ := Q.graph_energy_limits hg hf hvs hAslim
  have hkm : AEStronglyMeasurable (fun x => K-a*G x) ν :=
    (continuous_const.sub (continuous_const.mul hGc)).aestronglyMeasurable
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hkb : ∀ᵐ x ∂ν, |K-a*G x| ≤ |K|+|a| *CG := ae_of_all _ fun x =>
    (abs_sub _ _).trans (by rw [abs_mul]; gcongr; exact hGb x)
  apply heatVariableDissipation_of_energy_tendsto hnfin hID h hvS hfS hE hM hCξ hξb hkm
    (by positivity : 0 ≤ |K|+|a| *CG) hkb hT
  intro n
  exact hHess.rcd_weighted_heat_variable_generator hN hrcd hfull hfin o hF hFb hGb hGc ha h
    (hg n) (Nat.cast_nonneg n) hCξ (hvb n) hξb hξ0 hT
end WeakHessian

end
end

end OAI
